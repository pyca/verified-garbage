# rustls-verified-garbage

A [rustls](https://github.com/rustls/rustls) `CryptoProvider` whose
cryptography is verified-garbage's. It is a member of the library's
workspace, which the library's own tests, lints and coverage do not build
(they build only `verified-garbage`). It builds against rustls's 0.24
prerelease (the version in `Cargo.toml`), whose `CryptoProvider` API it
implements.

It aims to match rustls' aws-lc-rs provider:

| | |
|---|---|
| TLS 1.3 suites | AES-128-GCM-SHA256, AES-256-GCM-SHA384, CHACHA20-POLY1305-SHA256 |
| TLS 1.2 suites | ECDHE-{ECDSA,RSA} with AES-128-GCM, AES-256-GCM, CHACHA20-POLY1305 |
| Key exchange | X25519MLKEM768 (default, preferred), X25519, secp256r1, secp384r1; also SECP256R1MLKEM768, MLKEM768, MLKEM1024 |
| Signing keys | RSA (PKCS #1 or PKCS #8, 2048–8192 bits; PKCS #1 v1.5 and PSS with SHA-256/384/512), ECDSA P-256/P-384/P-521 (SEC 1 or PKCS #8), Ed25519 and ML-DSA-44/65/87 (PKCS #8, seed form) |
| Verification | everything aws-lc-rs' provider verifies: ECDSA on P-256/P-384/P-521 with SHA-256/384/512, Ed25519, RSA PKCS #1 v1.5 and PSS, ML-DSA |
| Tickets | AES-256-GCM, keys rotated every 6 hours |
| QUIC | packet protection with each TLS 1.3 suite's AEAD; header protection with AES-ECB or ChaCha20 (RFC 9001 §5.4) |
| Randomness | the operating system's (`getrandom`), as the library uses |

Keys and signatures are parsed and written with
[rust-asn1](https://github.com/alex/rust-asn1).

Differences from the aws-lc-rs provider:

* **No HPKE**, so no Encrypted Client Hello.
* EC public keys in certificates must be uncompressed (verified-garbage has no
  point decompression); aws-lc-rs also accepts compressed ones.
* ECDSA signatures are deterministic (RFC 6979).
* Not FIPS-validated.

## What is not verified

The primitives are verified-garbage's, and so is TLS 1.3's HKDF
(`verified_garbage::kdf::hkdf`). The provider is Rust, tested but not
proven, as rustls is. Most of it only adapts rustls's traits to the
library's API, but some of it is cryptography of its own:

* **ECDH key generation on P-256 and P-384** (`src/kx.rs`) is rejection
  sampling in Rust (FIPS 186-5 §A.4.2). It draws a candidate from the
  operating system, and derives the public key, which rejects a candidate
  outside `[1, n − 1]`, until one is accepted. The library has no verified
  EC key generation.
* **QUIC header protection** (`src/quic.rs`) is RFC 9001 §5.4.1: it masks
  the first byte's low bits and the packet number with the mask from the
  verified AES-ECB or ChaCha20, as rustls's own providers do.
* **TLS 1.2's PRF** is rustls's `PrfUsingHmac` over the verified HMAC.
* **Session tickets** (`src/ticketer.rs`) are sealed with the verified
  AES-256-GCM. The provider lays out
  the ticket (key name, random nonce, ciphertext, tag), authenticates the
  key name as associated data, and compares it with `subtle`.
* Keys and signatures are parsed and encoded with rust-asn1 (`src/der.rs`).

## Testing

The provider runs rustls's own API test suite. `rustls/setup.sh` checks
out rustls at that release's tag, by default into the workspace's
`target/rustls`, and applies `rustls/tests.patch`. The patch adds a
`tests_with_verified_garbage` module, which runs the suite with this
provider:

```sh
crates/rustls-verified-garbage/rustls/setup.sh
(cd target/rustls && cargo test -p rustls-test --test api tests_with_verified_garbage)
```

Every test passes, QUIC's included.

The signature verification algorithms and HKDF are tested against
Wycheproof, and every suite's record encryption against itself
(`tests/records.rs`):

```sh
WYCHEPROOF_ROOT=/path/to/wycheproof cargo test -p rustls-verified-garbage --release
```

CI runs all of them (`rustls-provider` in `.github/workflows/ci.yml`).
