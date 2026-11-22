# rustls-verified-garbage

A [rustls](https://github.com/rustls/rustls) `CryptoProvider` whose
cryptography is verified-garbage's. It builds against rustls 0.24.0-dev.3.

| | |
|---|---|
| TLS 1.3 suites | AES-128-GCM-SHA256, AES-256-GCM-SHA384, CHACHA20-POLY1305-SHA256 |
| TLS 1.2 suites | ECDHE-{ECDSA,RSA} with AES-128-GCM, AES-256-GCM, CHACHA20-POLY1305 |
| Key exchange | X25519MLKEM768 (default, preferred), X25519, secp256r1, secp384r1; also SECP256R1MLKEM768, MLKEM768, MLKEM1024 |
| Signing keys | RSA (PKCS #1 or PKCS #8, 2048–8192 bits; PKCS #1 v1.5 and PSS with SHA-256/384/512), ECDSA P-256/P-384/P-521 (SEC 1 or PKCS #8), Ed25519 and ML-DSA-44/65/87 (PKCS #8, seed form) |
| Verification | ECDSA on P-256/P-384/P-521 with SHA-256/384/512 (public keys compressed or not), Ed25519, RSA PKCS #1 v1.5 and PSS (2048–8192 bits), ML-DSA-44/65/87 |
| Tickets | AES-256-GCM, keys rotated every 6 hours |
| QUIC | packet protection with each TLS 1.3 suite's AEAD; header protection with AES-ECB or ChaCha20 (RFC 9001 §5.4) |
| Randomness | the operating system's (`getrandom`) |

Limitations:

* **No HPKE**, so no Encrypted Client Hello.

## Testing

The provider runs rustls's own API test suite. `rustls/setup.sh` checks
out rustls at that release's tag, by default into `target/rustls`, and
applies `rustls/tests.patch`. The patch adds a
`tests_with_verified_garbage` module, which runs the suite with this
provider:

```sh
crates/rustls-verified-garbage/rustls/setup.sh
(cd target/rustls && cargo test -p rustls-test --test api tests_with_verified_garbage)
```

Every test passes, QUIC's included.

Its own tests cover every line of it:

```sh
cargo test -p rustls-verified-garbage
```

CI runs all of them (`rustls-provider` in `.github/workflows/ci.yml`).

## Benchmarks

`bench/run.sh [rounds]` (Linux) runs everything
[`bench/RESULTS.md`](bench/RESULTS.md) reports, verified-garbage against
aws-lc-rs, each pinned to one CPU (`BENCH_CPU`, default 2), into
`target/bench-results`, and summarizes it with `bench/summarize.py`:

* rustls-bench's whole suite, `rounds` times (default 5) per provider, from
  the rustls checkout `rustls/setup.sh` makes in `target/rustls` (if
  there is none yet), whose `bench.patch` adds the `verified-garbage` provider;
* `provider-primitives`, a binary the patch adds to rustls-bench, which
  times both providers' primitives through the rustls traits (key exchange,
  signing, verification, records, HKDF, tickets);
* `bench/aws-lc-compare`, which times both libraries' primitives through
  their own APIs (with RSA keys it generates with `openssl`), to tell the
  library's costs from the provider's, and the AEADs at sizes up to 2 KiB.

To compare the providers on one thing, e.g. a cipher suite's bulk throughput:

```sh
target/rustls/target/release/rustls-bench --provider verified-garbage bulk TLS13_AES_128_GCM_SHA256
target/rustls/target/release/rustls-bench --provider aws-lc-rs bulk TLS13_AES_128_GCM_SHA256
```
