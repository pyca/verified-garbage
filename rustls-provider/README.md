# rustls-verified-garbage

A [rustls](https://github.com/rustls/rustls) `CryptoProvider` whose
cryptography is verified-garbage's. It is a package of its own (like
`bench/`), so the library's tests, lints and coverage never build rustls, and
it builds against rustls from git (the revision in `Cargo.toml`).

It aims to match rustls' aws-lc-rs provider:

| | |
|---|---|
| TLS 1.3 suites | AES-128-GCM-SHA256, AES-256-GCM-SHA384, CHACHA20-POLY1305-SHA256 |
| TLS 1.2 suites | ECDHE-{ECDSA,RSA} with AES-128-GCM, AES-256-GCM, CHACHA20-POLY1305 |
| Key exchange | X25519MLKEM768 (default, preferred), X25519, secp256r1, secp384r1; also SECP256R1MLKEM768, MLKEM768, MLKEM1024 |
| Signing keys | RSA (PKCS #1 or PKCS #8, 2048–8192 bits; PKCS #1 v1.5 and PSS with SHA-256/384/512), ECDSA P-256/P-384/P-521 (SEC 1 or PKCS #8), Ed25519 and ML-DSA-44/65/87 (PKCS #8, seed form) |
| Verification | everything aws-lc-rs' provider verifies: ECDSA on P-256/P-384/P-521 with SHA-256/384/512, Ed25519, RSA PKCS #1 v1.5 and PSS, ML-DSA |
| Tickets | AES-256-GCM, keys rotated every 6 hours |
| Randomness | the operating system's (`getrandom`), as the library uses |

Keys and signatures are parsed and written with
[rust-asn1](https://github.com/alex/rust-asn1).

Differences from the aws-lc-rs provider:

* **QUIC works only with ChaCha20-Poly1305 packet protection.** QUIC's header
  protection for the AES suites is AES-ECB of one block (RFC 9001 §5.4.3),
  which verified-garbage does not expose, so the AES suites have no QUIC
  support; and QUIC always protects its Initial packets with
  AES-128-GCM, so in practice QUIC does not work.
* **No HPKE**, so no Encrypted Client Hello.
* EC public keys in certificates must be uncompressed (verified-garbage has no
  point decompression); aws-lc-rs also accepts compressed ones.
* ECDSA signatures are deterministic (RFC 6979).
* ECDSA with a hash other than the curve's own (e.g. P-384 with SHA-256) is
  verified through the curve's verified function, given the hash value that
  FIPS 186-5 §6.4.2 derives (`e`, its leftmost bits or zero-extended).
* Not FIPS-validated.

## Testing

The provider runs rustls' own API test suite: `bench/setup-rustls.sh`
checks out rustls at the pinned revision and patches it (`bench/rustls.patch`)
to add a `tests_with_verified_garbage` module and a `verified-garbage`
provider to `rustls-bench`:

```sh
bench/setup-rustls.sh target/rustls
(cd target/rustls && cargo test -p rustls-test --test api tests_with_verified_garbage)
```

Every test passes but the five QUIC tests that need AES header protection.

The signature verification algorithms are tested against Wycheproof:

```sh
WYCHEPROOF_ROOT=/path/to/wycheproof cargo test --release
```

## Benchmarks

The patched rustls-bench takes `--provider verified-garbage`, and its
`provider-primitives` binary times both providers' primitives through the
rustls traits (key exchange, signing, verification, records, HKDF,
tickets). Results and analysis: [`bench/RESULTS.md`](bench/RESULTS.md).

```sh
(cd target/rustls && cargo build --profile=bench -p rustls-bench --features aws-lc-rs,verified-garbage)
target/rustls/target/release/rustls-bench --provider verified-garbage --api buffered
target/rustls/target/release/rustls-bench --provider aws-lc-rs --api buffered
target/rustls/target/release/provider-primitives
```
