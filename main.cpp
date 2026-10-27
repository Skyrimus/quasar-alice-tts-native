// Quasar Unofficial Alice TTS
// Copyright (c) Skyrimus 2026. MIT License (see LICENSE).

#include <openssl/ssl.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <alsa/asoundlib.h>
#include <opus/opus.h>

#include <arpa/inet.h>
#include <fcntl.h>
#include <netdb.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>

#include <algorithm>
#include <array>
#include <cctype>
#include <cerrno>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace tts {

#ifdef TTS_TEST_LOCALHOST
constexpr const char *kHost = "localhost";
constexpr const char *kPort = "18765";
#else
constexpr const char *kHost = "uniproxy.alice.yandex.net";
constexpr const char *kPort = "443";
#endif
constexpr const char *kPath = "/uni.ws";
constexpr const char *kDeviceUuidJson = "/data/quasar/quasar_metricad.json";
constexpr const char *kDeviceAccountStorage = "/data/quasar/account_storage.dat";
constexpr const char *kDeviceCaBundle = "/system/vendor/quasar/ca-certificates.crt";
constexpr size_t kMaxStorage = 16 * 1024 * 1024;
constexpr size_t kMaxMessage = 2 * 1024 * 1024;
constexpr size_t kMaxAudio = 16 * 1024 * 1024;
constexpr size_t kMaxText = 32768;
using Clock = std::chrono::steady_clock;
using Deadline = Clock::time_point;

[[noreturn]] void fail(const std::string &message) { throw std::runtime_error(message); }

std::string read_file(const std::string &path, size_t limit) {
  std::ifstream stream(path, std::ios::binary);
  if (!stream) fail("Cannot open input file: " + path);
  std::string out;
  char buffer[8192];
  while (stream) {
    stream.read(buffer, sizeof(buffer));
    auto count = stream.gcount();
    if (count <= 0) break;
    if (out.size() + static_cast<size_t>(count) > limit)
      fail("Input file exceeds the size limit");
    out.append(buffer, static_cast<size_t>(count));
  }
  if (!stream.eof()) fail("Cannot read input file");
  return out;
}

struct Field {
  uint32_t id = 0;
  uint8_t wire = 0;
  uint64_t number = 0;
  std::string bytes;
};

uint64_t read_varint(const std::string &data, size_t &pos) {
  uint64_t out = 0;
  for (unsigned i = 0; i < 10; ++i) {
    if (pos >= data.size()) fail("Truncated protobuf varint");
    uint8_t c = static_cast<uint8_t>(data[pos++]);
    if (i == 9 && c > 1) fail("Invalid oversized protobuf varint");
    out |= static_cast<uint64_t>(c & 0x7f) << (7 * i);
    if (!(c & 0x80)) return out;
  }
  fail("Invalid protobuf varint");
}

std::vector<Field> protobuf(const std::string &data) {
  if (data.size() > kMaxStorage) fail("Protobuf exceeds size limit");
  size_t pos = 0;
  std::vector<Field> fields;
  while (pos < data.size()) {
    if (fields.size() >= 100000) fail("Too many protobuf fields");
    uint64_t tag = read_varint(data, pos);
    Field field;
    if ((tag >> 3) > std::numeric_limits<uint32_t>::max() || !(tag >> 3))
      fail("Invalid protobuf field number");
    field.id = static_cast<uint32_t>(tag >> 3);
    field.wire = static_cast<uint8_t>(tag & 7);
    switch (field.wire) {
      case 0:
        field.number = read_varint(data, pos);
        break;
      case 1:
        if (data.size() - pos < 8) fail("Truncated protobuf fixed64");
        pos += 8;
        break;
      case 2: {
        uint64_t size = read_varint(data, pos);
        if (size > data.size() - pos) fail("Truncated protobuf bytes");
        field.bytes.assign(data, pos, static_cast<size_t>(size));
        pos += static_cast<size_t>(size);
        break;
      }
      case 5:
        if (data.size() - pos < 4) fail("Truncated protobuf fixed32");
        pos += 4;
        break;
      default:
        fail("Unsupported protobuf wire type");
    }
    fields.emplace_back(std::move(field));
  }
  return fields;
}

std::string last_bytes(const std::vector<Field> &fields, uint32_t id) {
  for (auto it = fields.rbegin(); it != fields.rend(); ++it)
    if (it->id == id && it->wire == 2) return it->bytes;
  return {};
}

struct Auth {
  size_t account_count = 0;
  std::string token;
  bool legacy = false;
  bool x_present = false;
  bool refresh_present = false;
};

Auth read_auth(const std::string &path, size_t index) {
  const auto root = protobuf(read_file(path, kMaxStorage));
  std::vector<std::string> accounts;
  for (const auto &f : root)
    if (f.id == 1 && f.wire == 2) accounts.emplace_back(f.bytes);
  if (index == 0 || index > accounts.size()) fail("Account index out of range");
  const auto fields = protobuf(accounts[index - 1]);
  Auth auth;
  auth.account_count = accounts.size();
  auto legacy_auth = last_bytes(fields, 3);
  auto modern_auth = last_bytes(fields, 8);
  if (!modern_auth.empty())
    auth.token = last_bytes(protobuf(modern_auth), 1);
  if (auth.token.empty()) {
    auth.token = std::move(legacy_auth);
    auth.legacy = !auth.token.empty();
  }
  auth.x_present = !last_bytes(fields, 2).empty() ||
                   !last_bytes(fields, 7).empty();
  auth.refresh_present = !last_bytes(fields, 4).empty();
  if (auth.token.size() > 16384) fail("Unexpected Auth-token size");
  for (unsigned char c : auth.token)
    if (c < 0x21 || c > 0x7e) fail("Auth-token contains invalid bytes");
  return auth;
}

void validate_uuid(const std::string &value) {
  if (value.empty() || value.size() > 200) fail("Invalid UUID length");
  for (unsigned char c : value)
    if (c < 0x21 || c > 0x7e) fail("UUID contains invalid bytes");
}

std::string json_escape(const std::string &s) {
  static constexpr char kHex[] = "0123456789abcdef";
  std::string out;
  out.reserve(s.size() + 16);
  out.push_back('"');
  for (unsigned char c : s) {
    switch (c) {
      case '"': out += "\\\""; break;
      case '\\': out += "\\\\"; break;
      case '\n': out += "\\n"; break;
      case '\r': out += "\\r"; break;
      case '\t': out += "\\t"; break;
      default:
        if (c < 32) {
          out += "\\u00";
          out.push_back(kHex[c >> 4]);
          out.push_back(kHex[c & 15]);
        } else {
          out.push_back(static_cast<char>(c));
        }
    }
  }
  out.push_back('"');
  return out;
}

std::string random_uuid() {
  std::array<unsigned char, 16> bytes{};
  if (RAND_bytes(bytes.data(), bytes.size()) != 1) fail("Secure randomness failed");
  bytes[6] = (bytes[6] & 0x0f) | 0x40;
  bytes[8] = (bytes[8] & 0x3f) | 0x80;
  static constexpr char kHex[] = "0123456789abcdef";
  std::string out;
  for (size_t i = 0; i < bytes.size(); ++i) {
    if (i == 4 || i == 6 || i == 8 || i == 10) out += '-';
    out += kHex[bytes[i] >> 4];
    out += kHex[bytes[i] & 15];
  }
  return out;
}

std::string event(const std::string &ns, const std::string &name,
                  const std::string &id, const std::string &payload_json) {
  return "{\"event\":{\"header\":{\"namespace\":" + json_escape(ns) +
         ",\"name\":" + json_escape(name) + ",\"messageId\":" +
         json_escape(id) + "},\"payload\":" + payload_json + "}}";
}

struct Json {
  enum class Kind { Null, Boolean, Number, String, Object, Array };
  Kind kind = Kind::Null;
  int64_t number = 0;
  bool boolean = false;
  std::string string;
  std::vector<std::pair<std::string, Json>> object;
  std::vector<Json> array;
  const Json *get(const std::string &key) const {
    if (kind != Kind::Object) return nullptr;
    for (const auto &entry : object)
      if (entry.first == key) return &entry.second;
    return nullptr;
  }
  std::string str() const { return kind == Kind::String ? string : ""; }
  bool is_nonzero() const {
    if (kind == Kind::Boolean) return boolean;
    if (kind == Kind::Number) return number != 0;
    if (kind == Kind::String) return !string.empty();
    return kind == Kind::Object || kind == Kind::Array;
  }
};

class JsonReader {
  const std::string &input_;
  size_t pos_ = 0;
  void ws() {
    while (pos_ < input_.size() && (input_[pos_] == ' ' ||
           input_[pos_] == '\r' || input_[pos_] == '\n' || input_[pos_] == '\t')) ++pos_;
  }
  bool eat(char c) {
    ws();
    if (pos_ < input_.size() && input_[pos_] == c) { ++pos_; return true; }
    return false;
  }
  void expect(char c) { if (!eat(c)) fail("Invalid JSON syntax"); }
  int hex() {
    if (pos_ >= input_.size()) fail("Invalid JSON unicode escape");
    char c = input_[pos_++];
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    fail("Invalid JSON unicode escape");
  }
  uint32_t unit() {
    uint32_t val = 0;
    for (int i = 0; i < 4; ++i) val = (val << 4) | hex();
    return val;
  }
  static void utf8(std::string &s, uint32_t c) {
    if (c < 0x80) s += static_cast<char>(c);
    else if (c < 0x800) {
      s += static_cast<char>(0xc0 | (c >> 6));
      s += static_cast<char>(0x80 | (c & 63));
    } else if (c < 0x10000) {
      s += static_cast<char>(0xe0 | (c >> 12));
      s += static_cast<char>(0x80 | ((c >> 6) & 63));
      s += static_cast<char>(0x80 | (c & 63));
    } else {
      s += static_cast<char>(0xf0 | (c >> 18));
      s += static_cast<char>(0x80 | ((c >> 12) & 63));
      s += static_cast<char>(0x80 | ((c >> 6) & 63));
      s += static_cast<char>(0x80 | (c & 63));
    }
  }
  std::string string() {
    expect('"');
    std::string out;
    while (pos_ < input_.size()) {
      unsigned char c = static_cast<unsigned char>(input_[pos_++]);
      if (c == '"') return out;
      if (c < 32) fail("Invalid control character in JSON string");
      if (c != '\\') { out += static_cast<char>(c); continue; }
      if (pos_ >= input_.size()) fail("Truncated JSON escape");
      char e = input_[pos_++];
      switch (e) {
        case '"': case '\\': case '/': out += e; break;
        case 'b': out += '\b'; break;
        case 'f': out += '\f'; break;
        case 'n': out += '\n'; break;
        case 'r': out += '\r'; break;
        case 't': out += '\t'; break;
        case 'u': {
          uint32_t u = unit();
          if (u >= 0xd800 && u <= 0xdbff) {
            if (pos_ + 2 > input_.size() || input_[pos_++] != '\\' || input_[pos_++] != 'u')
              fail("Incomplete JSON surrogate pair");
            uint32_t v = unit();
            if (v < 0xdc00 || v > 0xdfff) fail("Invalid JSON surrogate pair");
            u = 0x10000 + ((u - 0xd800) << 10) + (v - 0xdc00);
          } else if (u >= 0xdc00 && u <= 0xdfff) fail("Unpaired JSON surrogate");
          utf8(out, u);
          break;
        }
        default: fail("Invalid JSON escape");
      }
    }
    fail("Unterminated JSON string");
  }
  Json value(int depth) {
    if (depth > 32) fail("JSON nesting too deep");
    ws();
    if (pos_ >= input_.size()) fail("Unexpected end of JSON");
    Json out;
    char c = input_[pos_];
    if (c == '{') {
      out.kind = Json::Kind::Object;
      ++pos_;
      if (eat('}')) return out;
      do {
        ws();
        if (pos_ >= input_.size() || input_[pos_] != '"') fail("Invalid JSON object key");
        auto k = string();
        expect(':');
        auto v = value(depth + 1);
        out.object.emplace_back(std::move(k), std::move(v));
        if (out.object.size() > 20000) fail("Too many JSON properties");
        if (eat('}')) return out;
        expect(',');
      } while (true);
    }
    if (c == '[') {
      out.kind = Json::Kind::Array;
      ++pos_;
      if (eat(']')) return out;
      do {
        out.array.emplace_back(value(depth + 1));
        if (out.array.size() > 20000) fail("JSON array too large");
        if (eat(']')) return out;
        expect(',');
      } while (true);
    }
    if (c == '"') {
      out.kind = Json::Kind::String;
      out.string = string();
      return out;
    }
    auto literal = [&](const char *word) {
      size_t n = std::strlen(word);
      if (input_.compare(pos_, n, word)) fail("Invalid JSON literal");
      pos_ += n;
    };
    if (c == 't') { literal("true"); out.kind = Json::Kind::Boolean; out.boolean = true; return out; }
    if (c == 'f') { literal("false"); out.kind = Json::Kind::Boolean; return out; }
    if (c == 'n') { literal("null"); return out; }
    if (c == '-' || (c >= '0' && c <= '9')) {
      size_t start = pos_;
      if (c == '-') ++pos_;
      if (pos_ >= input_.size()) fail("Invalid JSON number");
      if (input_[pos_] == '0') ++pos_;
      else {
        if (input_[pos_] < '1' || input_[pos_] > '9') fail("Invalid JSON number");
        while (pos_ < input_.size() && std::isdigit(static_cast<unsigned char>(input_[pos_]))) ++pos_;
      }
      if (pos_ < input_.size() && input_[pos_] == '.') {
        ++pos_;
        if (pos_ >= input_.size() || !std::isdigit(static_cast<unsigned char>(input_[pos_]))) fail("Invalid JSON fraction");
        while (pos_ < input_.size() && std::isdigit(static_cast<unsigned char>(input_[pos_]))) ++pos_;
      }
      if (pos_ < input_.size() && (input_[pos_] == 'e' || input_[pos_] == 'E')) {
        ++pos_;
        if (pos_ < input_.size() && (input_[pos_] == '+' || input_[pos_] == '-')) ++pos_;
        if (pos_ >= input_.size() || !std::isdigit(static_cast<unsigned char>(input_[pos_]))) fail("Invalid JSON exponent");
        while (pos_ < input_.size() && std::isdigit(static_cast<unsigned char>(input_[pos_]))) ++pos_;
      }
      out.kind = Json::Kind::Number;
      const auto repr = input_.substr(start, pos_ - start);
      char *end = nullptr;
      errno = 0;
      long long n = std::strtoll(repr.c_str(), &end, 10);
      if (!errno && end && *end == '\0') out.number = n;
      return out;
    }
    fail("Invalid JSON value");
  }
public:
  explicit JsonReader(const std::string &input): input_(input) {
    if (input.size() > kMaxMessage) fail("JSON response too large");
  }
  Json parse() {
    Json result = value(0);
    ws();
    if (pos_ != input_.size()) fail("Extra bytes after JSON");
    return result;
  }
};

class WebSocket {
  int fd_ = -1;
  SSL_CTX *ctx_ = nullptr;
  SSL *ssl_ = nullptr;
  Deadline deadline_;

  static int remaining_ms(Deadline limit) {
    auto left = std::chrono::duration_cast<std::chrono::milliseconds>(limit - Clock::now()).count();
    if (left <= 0) fail("Network timeout");
    return static_cast<int>(std::min<int64_t>(left, std::numeric_limits<int>::max()));
  }
  static void wait_fd(int fd, short events, Deadline limit) {
    pollfd pfd{fd, events, 0};
    for (;;) {
      int result = poll(&pfd, 1, remaining_ms(limit));
      if (result > 0) {
        if (pfd.revents & POLLNVAL) fail("Invalid socket descriptor");
        if (pfd.revents & (events | POLLERR | POLLHUP)) return;
      } else if (result == 0) fail("Network timeout");
      else if (errno != EINTR) fail("Socket poll failed");
    }
  }
  void connect_tcp(Deadline limit) {
    addrinfo hints{};
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;
    addrinfo *result = nullptr;
    if (getaddrinfo(kHost, kPort, &hints, &result) != 0) fail("DNS lookup failed");
    std::unique_ptr<addrinfo, decltype(&freeaddrinfo)> addresses(result, freeaddrinfo);
    for (auto *p = result; p; p = p->ai_next) {
      int fd = socket(p->ai_family, p->ai_socktype, p->ai_protocol);
      if (fd < 0) continue;
      auto flags = fcntl(fd, F_GETFL, 0);
      if (flags < 0 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) { close(fd); continue; }
      int rc = connect(fd, p->ai_addr, p->ai_addrlen);
      if (rc != 0 && errno == EINPROGRESS) {
        try {
          wait_fd(fd, POLLOUT, limit);
        } catch (...) { close(fd); throw; }
        int err = 0;
        socklen_t len = sizeof(err);
        if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &len) != 0 || err != 0) rc = -1;
        else rc = 0;
      }
      if (!rc) { fd_ = fd; return; }
      close(fd);
    }
    fail("TCP connection failed");
  }

  void ssl_wait(int code, Deadline limit, const char *phase) {
    const int saved_errno = errno;
    const int ssl_error = SSL_get_error(ssl_, code);
    switch (ssl_error) {
      case SSL_ERROR_WANT_READ: wait_fd(fd_, POLLIN, limit); return;
      case SSL_ERROR_WANT_WRITE: wait_fd(fd_, POLLOUT, limit); return;
    }
    std::string why = "TLS ";
    why += phase;
    why += " failed: ";
    switch (ssl_error) {
      case SSL_ERROR_ZERO_RETURN: why += "connection closed (close_notify)"; break;
      case SSL_ERROR_SSL: why += "protocol/certificate error"; break;
      case SSL_ERROR_SYSCALL:
        why += "socket I/O error";
        if (code == 0) why += " (unexpected EOF)";
        else if (saved_errno && saved_errno != EINTR && saved_errno != EAGAIN &&
                 saved_errno != EWOULDBLOCK)
          why += " (errno=" + std::to_string(saved_errno) + ": " +
                 std::string(strerror(saved_errno)) + ")";
        break;
      default: why += "SSL_get_error=" + std::to_string(ssl_error); break;
    }
    const long verify = SSL_get_verify_result(ssl_);
    if (verify != X509_V_OK) {
      why += "; certificate verify=" + std::to_string(verify);
      why += " (";
      why += X509_verify_cert_error_string(verify);
      why += ")";
    }
    unsigned long err = ERR_peek_last_error();
    if (err != 0) {
      if (const char *reason = ERR_reason_error_string(err)) {
        why += "; OpenSSL reason=";
        why += reason;
      } else {
        why += "; OpenSSL code=" + std::to_string(err);
      }
    }
    fail(why);
  }
  void write_all(const unsigned char *data, size_t size, Deadline limit) {
    size_t pos = 0;
    while (pos < size) {
      int amount = static_cast<int>(std::min<size_t>(size - pos, 16384));
      int sent = SSL_write(ssl_, data + pos, amount);
      if (sent > 0) pos += static_cast<size_t>(sent);
      else ssl_wait(sent, limit, "write");
    }
  }
  void read_all(unsigned char *data, size_t size, Deadline limit) {
    size_t pos = 0;
    while (pos < size) {
      int n = SSL_read(ssl_, data + pos, static_cast<int>(std::min<size_t>(size - pos, 16384)));
      if (n > 0) pos += static_cast<size_t>(n);
      else ssl_wait(n, limit, "read");
    }
  }
  static std::string lower(const std::string &s) {
    std::string out = s;
    for (auto &c : out) c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    return out;
  }
  static std::string trim(const std::string &s) {
    auto l = s.find_first_not_of(" \t\r\n");
    if (l == std::string::npos) return "";
    auto r = s.find_last_not_of(" \t\r\n");
    return s.substr(l, r - l + 1);
  }
  static std::string base64(const unsigned char *data, size_t n) {
    std::string output(4 * ((n + 2) / 3), '\0');
    EVP_EncodeBlock(reinterpret_cast<unsigned char *>(&output[0]), data, static_cast<int>(n));
    return output;
  }
  void upgrade(const std::string &device_uuid, const std::string &token, Deadline limit) {
    std::array<unsigned char, 16> nonce{};
    if (RAND_bytes(nonce.data(), nonce.size()) != 1) fail("Secure randomness failed");
    auto key = base64(nonce.data(), nonce.size());
    std::string request = std::string("GET ") + kPath + " HTTP/1.1\r\nHost: " + kHost +
      "\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: " + key +
      "\r\nSec-WebSocket-Version: 13\r\nX-UPRX-UUID: " + device_uuid +
      "\r\nX-UPRX-AUTH-TOKEN: " + token + "\r\nUser-Agent: quasar-tts-cpp/1.0\r\n\r\n";
    write_all(reinterpret_cast<const unsigned char *>(request.data()), request.size(), limit);
    // Remove the HTTP request (containing credentials) from memory as soon as
    // possible; never include it in exceptions or logs.
    OPENSSL_cleanse(&request[0], request.size());
    std::string response;
    response.reserve(1024);
    while (response.size() < 16384 && (response.size() < 4 || response.compare(response.size() - 4, 4, "\r\n\r\n"))) {
      unsigned char c = 0;
      read_all(&c, 1, limit);
      response.push_back(static_cast<char>(c));
    }
    if (response.size() >= 16384) fail("Excessive WebSocket response headers");
    auto eol = response.find("\r\n");
    if (eol == std::string::npos) fail("Malformed HTTP/WebSocket status line");
    auto status_line = response.substr(0, eol);
    auto first_space = status_line.find(' ');
    if (first_space == std::string::npos || first_space + 4 > status_line.size())
      fail("Malformed HTTP/WebSocket status line");
    std::string status_code = status_line.substr(first_space + 1, 3);
    if (status_code.size() != 3 || !std::all_of(status_code.begin(), status_code.end(),
                      [](unsigned char c) { return std::isdigit(c); }))
      fail("Malformed HTTP/WebSocket status line");
    if (status_code != "101") fail("WebSocket upgrade rejected (HTTP " + status_code + ")");
    std::string accept, upgrade, connection;
    size_t pos = eol + 2;
    while (pos < response.size()) {
      auto end = response.find("\r\n", pos);
      if (end == std::string::npos || end == pos) break;
      auto colon = response.find(':', pos);
      if (colon == std::string::npos || colon >= end) fail("Malformed WebSocket response");
      auto k = lower(trim(response.substr(pos, colon - pos)));
      auto v = trim(response.substr(colon + 1, end - colon - 1));
      if (k == "sec-websocket-accept") accept = v;
      if (k == "upgrade") upgrade = lower(v);
      if (k == "connection") connection = lower(v);
      pos = end + 2;
    }
    std::string combined = key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
    std::array<unsigned char, EVP_MAX_MD_SIZE> sha{};
    unsigned int sha_len = 0;
    if (EVP_Digest(combined.data(), combined.size(), sha.data(), &sha_len, EVP_sha1(), nullptr) != 1)
      fail("WebSocket handshake digest failed");
    if (sha_len != 20 || accept != base64(sha.data(), sha_len) ||
        upgrade != "websocket" || connection.find("upgrade") == std::string::npos)
      fail("WebSocket handshake verification failed");
  }
  struct Frame { uint8_t opcode; bool fin; std::string payload; };
  Frame read_frame(Deadline limit) {
    unsigned char h[2];
    read_all(h, 2, limit);
    if (h[0] & 0x70) fail("Unsupported WebSocket extensions");
    if (h[1] & 0x80) fail("Server sent a masked WebSocket frame");
    Frame frame{};
    frame.fin = (h[0] & 0x80) != 0;
    frame.opcode = h[0] & 0x0f;
    uint64_t n = h[1] & 0x7f;
    if (n == 126) {
      unsigned char ext[2]; read_all(ext, 2, limit);
      n = (uint64_t(ext[0]) << 8) | ext[1];
    } else if (n == 127) {
      unsigned char ext[8]; read_all(ext, 8, limit);
      n = 0;
      for (unsigned char c : ext) n = (n << 8) | c;
    }
    if (n > kMaxMessage) fail("WebSocket frame exceeds maximum size");
    if (frame.opcode >= 8 && (!frame.fin || n > 125)) fail("Invalid WebSocket control frame");
    frame.payload.resize(static_cast<size_t>(n));
    if (n) read_all(reinterpret_cast<unsigned char *>(&frame.payload[0]), static_cast<size_t>(n), limit);
    return frame;
  }
  void send_frame(uint8_t opcode, const std::string &payload, Deadline limit) {
    std::vector<unsigned char> frame;
    frame.reserve(payload.size() + 14);
    frame.push_back(static_cast<unsigned char>(0x80 | opcode));
    auto n = payload.size();
    if (n < 126) frame.push_back(0x80 | static_cast<unsigned char>(n));
    else if (n <= 0xffff) {
      frame.push_back(0x80 | 126);
      frame.push_back((n >> 8) & 255);
      frame.push_back(n & 255);
    } else {
      frame.push_back(0x80 | 127);
      for (int shift = 56; shift >= 0; shift -= 8) frame.push_back((n >> shift) & 255);
    }
    unsigned char mask[4]{};
    if (RAND_bytes(mask, sizeof(mask)) != 1) fail("Secure randomness failed");
    frame.insert(frame.end(), mask, mask + 4);
    for (size_t i = 0; i < n; ++i) frame.push_back(static_cast<unsigned char>(payload[i]) ^ mask[i % 4]);
    write_all(frame.data(), frame.size(), limit);
  }
public:
  WebSocket(const std::string &device_uuid, const std::string &token,
            const std::string &ca_file, Deadline deadline)
      : deadline_(deadline) {
    auto handshake_limit = std::min(deadline, Clock::now() + std::chrono::seconds(15));
    try {
      connect_tcp(handshake_limit);
      ctx_ = SSL_CTX_new(TLS_client_method());
      if (!ctx_) fail("Cannot create TLS context");
      if (SSL_CTX_set_min_proto_version(ctx_, TLS1_2_VERSION) != 1)
        fail("TLS version configuration failed");
      const std::string effective_ca = !ca_file.empty() ? ca_file :
          (access(kDeviceCaBundle, F_OK) == 0 ? kDeviceCaBundle : "");
      if (!effective_ca.empty()) {
        if (SSL_CTX_load_verify_locations(ctx_, effective_ca.c_str(), nullptr) != 1)
          fail("Cannot load CA bundle: " + effective_ca + " (expected readable PEM)");
      } else if (SSL_CTX_set_default_verify_paths(ctx_) != 1) {
        fail("TLS default CA trust initialization failed (try --ca-file)");
      }
      SSL_CTX_set_verify(ctx_, SSL_VERIFY_PEER, nullptr);
      ssl_ = SSL_new(ctx_);
      if (!ssl_) fail("Cannot create TLS session");
      if (SSL_set_fd(ssl_, fd_) != 1 || SSL_set_tlsext_host_name(ssl_, kHost) != 1 ||
          SSL_set1_host(ssl_, kHost) != 1) fail("TLS hostname setup failed");
      for (;;) {
        int rc = SSL_connect(ssl_);
        if (rc == 1) break;
        ssl_wait(rc, handshake_limit, "handshake");
      }
      if (SSL_get_verify_result(ssl_) != X509_V_OK) fail("TLS certificate verification failed");
      upgrade(device_uuid, token, handshake_limit);
    } catch (...) {
      cleanup();
      throw;
    }
  }
  void cleanup() {
    if (ssl_) { SSL_free(ssl_); ssl_ = nullptr; }
    if (ctx_) { SSL_CTX_free(ctx_); ctx_ = nullptr; }
    if (fd_ >= 0) { close(fd_); fd_ = -1; }
  }
  ~WebSocket() { cleanup(); }
  WebSocket(const WebSocket &) = delete;
  WebSocket &operator=(const WebSocket &) = delete;
  void send_text(const std::string &text) { send_frame(0x1, text, deadline_); }
  struct Message { bool binary; std::string payload; };
  Message receive() {
    std::string assembled;
    int type = -1;
    for (;;) {
      auto f = read_frame(deadline_);
      if (f.opcode == 0x8) fail("UniProxy closed the WebSocket");
      if (f.opcode == 0x9) { send_frame(0xa, f.payload, deadline_); continue; }
      if (f.opcode == 0xa) continue;
      if (f.opcode == 0x1 || f.opcode == 0x2) {
        if (type != -1) fail("Interleaved WebSocket fragments");
        type = f.opcode;
      } else if (f.opcode != 0x0 || type == -1) fail("Invalid WebSocket opcode");
      if (assembled.size() + f.payload.size() > kMaxMessage) fail("WebSocket message too large");
      assembled += f.payload;
      if (f.fin) return {type == 0x2, std::move(assembled)};
    }
  }
};

class AlsaSink {
  snd_pcm_t *pcm_ = nullptr;
  std::string name_;
  unsigned channels_;
  size_t frames_ = 0;
public:
  AlsaSink(std::string name, unsigned channels): name_(std::move(name)), channels_(channels) {}
  ~AlsaSink() { if (pcm_) snd_pcm_close(pcm_); }
  AlsaSink(const AlsaSink &) = delete;
  AlsaSink &operator=(const AlsaSink &) = delete;
  void write(const int16_t *pcm, size_t frames, unsigned input_channels) {
    if (!frames) return;
    if (!pcm_) {
      int rc = snd_pcm_open(&pcm_, name_.c_str(), SND_PCM_STREAM_PLAYBACK, 0);
      if (rc < 0) fail(std::string("ALSA open failed: ") + snd_strerror(rc));
      rc = snd_pcm_set_params(pcm_, SND_PCM_FORMAT_S16_LE, SND_PCM_ACCESS_RW_INTERLEAVED,
                              channels_, 48000, 1, 100000);
      if (rc < 0) fail(std::string("ALSA configuration failed: ") + snd_strerror(rc));
    }
    std::vector<int16_t> converted;
    const int16_t *output = pcm;
    if (input_channels != channels_) {
      converted.resize(frames * channels_);
      for (size_t i = 0; i < frames; ++i) {
        if (channels_ == 2 && input_channels == 1) {
          converted[2 * i] = converted[2 * i + 1] = pcm[i];
        } else if (channels_ == 1 && input_channels == 2) {
          converted[i] = static_cast<int16_t>((int32_t(pcm[2 * i]) + pcm[2 * i + 1]) / 2);
        } else fail("Unsupported PCM channel conversion");
      }
      output = converted.data();
    }
    size_t written = 0;
    while (written < frames) {
      snd_pcm_sframes_t rc = snd_pcm_writei(pcm_, output + written * channels_, frames - written);
      if (rc < 0) {
        auto recovered = snd_pcm_recover(pcm_, static_cast<int>(rc), 1);
        if (recovered < 0) fail(std::string("ALSA playback error: ") + snd_strerror(recovered));
        continue;
      }
      if (!rc) fail("ALSA write made no progress");
      written += static_cast<size_t>(rc);
    }
    frames_ += frames;
  }
  void drain() {
    if (pcm_) {
      int rc = snd_pcm_drain(pcm_);
      if (rc < 0) fail(std::string("ALSA drain failed: ") + snd_strerror(rc));
    }
  }
  size_t frames() const { return frames_; }
};

class OpusToAlsa {
  AlsaSink &sink_;
  OpusDecoder *decoder_ = nullptr;
  unsigned channels_ = 0;
  unsigned preskip_ = 0;
  bool saw_head_ = false;
  size_t packets_ = 0;
  size_t decoded_frames_ = 0;
  void configure(unsigned channels, unsigned preskip) {
    if (decoder_) fail("Duplicate Opus header");
    if (channels < 1 || channels > 2) fail("Unsupported Opus channel count");
    int error = 0;
    decoder_ = opus_decoder_create(48000, static_cast<int>(channels), &error);
    if (!decoder_ || error != OPUS_OK) fail("Cannot initialize Opus decoder");
    channels_ = channels;
    preskip_ = preskip;
  }
public:
  explicit OpusToAlsa(AlsaSink &sink): sink_(sink) {}
  ~OpusToAlsa() { if (decoder_) opus_decoder_destroy(decoder_); }
  void packet(const unsigned char *data, size_t n) {
    if (!n) return;
    if (n >= 8 && !std::memcmp(data, "OpusHead", 8)) {
      if (n < 19 || data[8] == 0 || data[18] != 0) fail("Unsupported OpusHead header");
      if (saw_head_) fail("Multiple OpusHead headers");
      saw_head_ = true;
      configure(data[9], unsigned(data[10]) | (unsigned(data[11]) << 8));
      return;
    }
    if (n >= 8 && !std::memcmp(data, "OpusTags", 8)) return;
    if (!decoder_) {
      configure(1, 0);
    }
    if (n > static_cast<size_t>(std::numeric_limits<opus_int32>::max()))
      fail("Opus packet too large");
    std::array<int16_t, 5760 * 2> pcm{};
    int count = opus_decode(decoder_, data, static_cast<opus_int32>(n),
                            pcm.data(), 5760, 0);
    if (count < 0) fail("Malformed Opus audio packet or wrong framing");
    ++packets_;
    unsigned dropped = std::min(preskip_, static_cast<unsigned>(count));
    preskip_ -= dropped;
    unsigned playable = static_cast<unsigned>(count) - dropped;
    if (playable) {
      sink_.write(pcm.data() + size_t(dropped) * channels_, playable, channels_);
      decoded_frames_ += playable;
    }
  }
  size_t packets() const { return packets_; }
  size_t decoded_frames() const { return decoded_frames_; }
};

class AudioStream {
  OpusToAlsa opus_;
  enum class Format { Unknown, Ogg, Packets } format_ = Format::Unknown;
  std::vector<unsigned char> pending_;
  std::vector<unsigned char> packet_;
  size_t total_ = 0;
  void ogg_pages() {
    size_t offset = 0;
    while (pending_.size() - offset >= 27) {
      const unsigned char *p = pending_.data() + offset;
      if (std::memcmp(p, "OggS", 4) || p[4] != 0) fail("Invalid Ogg/Opus stream");
      size_t segments = p[26];
      if (pending_.size() - offset < 27 + segments) break;
      size_t payload = 0;
      for (size_t i = 0; i < segments; ++i) payload += p[27 + i];
      size_t page_bytes = 27 + segments + payload;
      if (pending_.size() - offset < page_bytes) break;
      if (!(p[5] & 1) && !packet_.empty()) fail("Broken Ogg packet continuation");
      size_t data_offset = 27 + segments;
      for (size_t i = 0; i < segments; ++i) {
        unsigned size = p[27 + i];
        if (packet_.size() + size > kMaxMessage) fail("Ogg packet too large");
        packet_.insert(packet_.end(), p + data_offset, p + data_offset + size);
        data_offset += size;
        if (size < 255) {
          opus_.packet(packet_.data(), packet_.size());
          packet_.clear();
        }
      }
      offset += page_bytes;
    }
    if (offset) pending_.erase(pending_.begin(), pending_.begin() + static_cast<std::ptrdiff_t>(offset));
  }
public:
  explicit AudioStream(AlsaSink &sink): opus_(sink) {}
  void push(const unsigned char *data, size_t n) {
    if (!n) return;
    if (total_ + n > kMaxAudio) fail("TTS stream exceeds 16 MiB");
    total_ += n;
    if (format_ == Format::Unknown) {
      if (!pending_.empty() || (n < 4 && !std::memcmp(data, "OggS", n))) {
        pending_.insert(pending_.end(), data, data + n);
        if (pending_.size() < 4) return;
        if (std::memcmp(pending_.data(), "OggS", 4))
          fail("Incomplete or inconsistent Ogg/Opus header");
        format_ = Format::Ogg;
        ogg_pages();
        return;
      }
      format_ = n >= 4 && !std::memcmp(data, "OggS", 4) ? Format::Ogg : Format::Packets;
    }
    if (format_ == Format::Ogg) {
      pending_.insert(pending_.end(), data, data + n);
      if (pending_.size() > kMaxMessage) fail("Ogg parser buffer too large");
      ogg_pages();
    } else {
      opus_.packet(data, n);
    }
  }
  void finish() {
    if (!pending_.empty() || !packet_.empty()) fail("Incomplete Ogg/Opus audio");
    if (!opus_.packets() || !opus_.decoded_frames()) fail("No Opus audio decoded");
  }
  size_t bytes() const { return total_; }
  size_t packets() const { return opus_.packets(); }
};

std::string uuid_from_file(const std::string &path) {
  const std::string content = read_file(path, 16 * 1024);
  const auto first = content.find_first_not_of(" \t\r\n");
  if (first == std::string::npos) fail("Empty device UUID file: " + path);
  std::string uuid;
  if (content[first] == '{') {
    Json root;
    try { root = JsonReader(content).parse(); }
    catch (const std::runtime_error &) { fail("Invalid device UUID JSON: " + path); }
    const Json *value = root.get("UUID");
    if (!value || value->kind != Json::Kind::String)
      fail("Device UUID JSON must contain a string field named UUID: " + path);
    uuid = value->string;
  } else {
    const auto last = content.find_last_not_of(" \t\r\n");
    uuid = content.substr(first, last - first + 1);
  }
  validate_uuid(uuid);
  return uuid;
}

struct Options {
  std::string storage = kDeviceAccountStorage;
  std::string uuid;
  std::string uuid_file;
  std::string ca_file;
  std::string voice = "shitova.us";
  std::string alsa = "default";
  std::string text;
  int timeout = 30;
  unsigned channels = 2;
  size_t account = 1;
  bool inspect = false;
  bool probe = false;
};

Options arguments(int argc, char **argv) {
  Options o;
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    auto next = [&]() -> std::string {
      if (i + 1 >= argc) fail("Missing argument for " + arg);
      return argv[++i];
    };
    if (arg == "--storage") o.storage = next();
    else if (arg == "--uuid") o.uuid = next();
    else if (arg == "--uuid-file") o.uuid_file = next();
    else if (arg == "--ca-file") o.ca_file = next();
    else if (arg == "--voice") o.voice = next();
    else if (arg == "--alsa") o.alsa = next();
    else if (arg == "--text") o.text = next();
    else if (arg == "--timeout") o.timeout = std::stoi(next());
    else if (arg == "--channels") o.channels = static_cast<unsigned>(std::stoi(next()));
    else if (arg == "--account") o.account = static_cast<size_t>(std::stoul(next()));
    else if (arg == "--inspect") o.inspect = true;
    else if (arg == "--probe") o.probe = true;
    else if (arg == "--help" || arg == "-h") {
      std::cout <<
          "quasar_tts --text TEXT [--alsa default] [--storage FILE]\n"
          "           [--voice shitova.us] [--channels 1|2] [--timeout 30]\n"
          "           [--account 1] [--uuid UUID|--uuid-file FILE] [--ca-file PEM]\n"
          "           [--inspect|--probe]\n"
          "Default storage: " << kDeviceAccountStorage << ".\n"
          "Default UUID:    " << kDeviceUuidJson << " (JSON field UUID).\n"
          "Default CA:   " << kDeviceCaBundle << " (if present).\n"
          "Reads device Auth-token from the account storage file and sends\n"
          "decoded 48000-Hz signed 16-bit PCM directly to ALSA.\n";
      std::exit(0);
    } else fail("Unknown command-line argument: " + arg);
  }
  if (o.timeout < 1 || o.timeout > 120) fail("Timeout must be in 1..120 seconds");
  if (o.channels != 1 && o.channels != 2) fail("ALSA channels must be 1 or 2");
  if (o.account < 1 || o.account > 1000) fail("Invalid account index");
  if (!o.uuid.empty() && !o.uuid_file.empty()) fail("Use only --uuid or --uuid-file");
  if (o.inspect && o.probe) fail("Choose either --inspect or --probe");
  if (o.text.size() > kMaxText) fail("TTS text is too long");
  if (!o.inspect && !o.probe && o.text.empty()) fail("--text is required");
  if (!o.inspect) {
    if (o.uuid.empty()) {
      const std::string path = !o.uuid_file.empty() ? o.uuid_file : kDeviceUuidJson;
      o.uuid = uuid_from_file(path);
    }
    validate_uuid(o.uuid);
  }
  if (o.voice.empty() || o.voice.size() > 200) fail("Invalid voice name");
  return o;
}

uint32_t stream_id(const Json *j) {
  if (!j || j->kind != Json::Kind::Number ||
      j->number < 0 || j->number > std::numeric_limits<uint32_t>::max())
    fail("Invalid TTS streamId");
  return static_cast<uint32_t>(j->number);
}

int run(const Options &opt) {
  auto auth = read_auth(opt.storage, opt.account);
  std::cout << "Account records: " << auth.account_count << "; selected: " << opt.account << '\n';
  std::cout << "Auth-token: " << (auth.token.empty() ? "absent" :
             (auth.legacy ? "present (legacy field 3)" : "present (modern field 8)")) << '\n';
  if (opt.inspect) {
    std::cout << "X-token: " << (auth.x_present ? "present" : "absent")
              << "; legacy refresh-token: " << (auth.refresh_present ? "present" : "absent") << '\n';
    return 0;
  }
  if (auth.token.empty()) fail("No Auth access-token in selected account");
  auto deadline = Clock::now() + std::chrono::seconds(opt.timeout);
  WebSocket ws(opt.uuid, auth.token, opt.ca_file, deadline);
  if (!auth.token.empty()) OPENSSL_cleanse(&auth.token[0], auth.token.size());
  auth.token.clear();
  std::cout << "WebSocket handshake: OK (not necessarily authenticated)\n";
  if (opt.probe) return 0;
  const auto sync_id = random_uuid();
  const auto id = random_uuid();
  auto state = "{\"uuid\":" + json_escape(opt.uuid) + ",\"lang\":\"ru-RU\",\"voice\":" +
               json_escape(opt.voice) + "}";
  ws.send_text(event("System", "SynchronizeState", sync_id, state));
  auto payload = "{\"voice\":" + json_escape(opt.voice) +
                 ",\"lang\":\"ru-RU\",\"format\":\"audio/opus\","
                 "\"emotion\":\"neutral\",\"quality\":\"UltraHigh\",\"text\":" +
                 json_escape(opt.text) + "}";
  ws.send_text(event("TTS", "Generate", id, payload));
  AlsaSink sink(opt.alsa, opt.channels);
  AudioStream audio(sink);
  bool has_stream = false;
  uint32_t expected = 0;
  size_t ignored_binary = 0;
  for (;;) {
    auto msg = ws.receive();
    if (msg.binary) {
      if (msg.payload.size() < 4 || !has_stream) continue;
      auto *b = reinterpret_cast<const unsigned char *>(msg.payload.data());
      uint32_t got = (uint32_t(b[0]) << 24) | (uint32_t(b[1]) << 16) |
                     (uint32_t(b[2]) << 8) | b[3];
      if (got == expected) audio.push(b + 4, msg.payload.size() - 4);
      else ++ignored_binary;
      continue;
    }
    Json root;
    try { root = JsonReader(msg.payload).parse(); }
    catch (const std::runtime_error &) { continue; }
    if (root.get("error")) fail("UniProxy returned an error");
    const Json *directive = root.get("directive");
    if (directive) {
      const Json *header = directive->get("header");
      if (header && header->get("refMessageId") && header->get("refMessageId")->str() == id) {
        const std::string name = header->get("name") ? header->get("name")->str() : "";
        if (name == "Error" || name == "Failure") fail("UniProxy rejected the TTS request");
        if (name == "Speak") {
          expected = stream_id(header->get("streamId"));
          has_stream = true;
        }
      }
    }
    const Json *control = root.get("streamcontrol");
    if (control && has_stream) {
      const Json *sid = control->get("streamId");
      if (!sid || sid->kind != Json::Kind::Number || sid->number != expected) continue;
      const Json *action = control->get("action");
      const Json *reason = control->get("reason");
      if ((action && action->is_nonzero()) || (reason && reason->is_nonzero()))
        fail("UniProxy aborted the TTS audio stream");
      audio.finish();
      sink.drain();
      std::cout << "TTS playback complete: " << audio.bytes() << " audio bytes, "
                << audio.packets() << " Opus packets, " << sink.frames() << " PCM frames\n";
      return 0;
    }
  }
}

}

#ifndef TTS_NO_MAIN
int main(int argc, char **argv) {
  try {
    return tts::run(tts::arguments(argc, argv));
  } catch (const std::exception &e) {
    std::cerr << "Error: " << e.what() << '\n';
    return 1;
  }
}
#endif
