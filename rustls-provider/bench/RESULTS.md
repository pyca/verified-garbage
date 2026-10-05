# rustls benchmarks: verified-garbage vs aws-lc-rs

Measured 2026-10-05 on one core (`taskset -c 2`) of an Intel Xeon at
2.1 GHz with SHA-NI, AVX-512 (IFMA, VAES, VPCLMULQDQ), ADX; rustls
91aebe5d, aws-lc-rs 1.18.1. Throughput is noisy on this VM (±10%):
ratios are what to read, and differences under ~10% are not significant.

## rustls-bench (`--api buffered`, median of 5 runs)

Ratios are verified-garbage / aws-lc-rs (below 1 is slower), geometric
means over the cipher suites of each row.

| | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 0.11–0.15 | 0.16–0.24 | 0.10–0.13 | 0.10–0.13 | 0.90–1.00 | 1.08–1.27 |
| RSA-2048 | 0.42–0.47 | 0.93 | 0.68–0.71 | 0.73–0.77 | 0.83–0.97 | 1.03–1.44 |
| Ed25519 | 0.73–0.74 | 0.78–0.83 | 0.72–0.74 | 0.74–0.76 | 0.92–1.03 | 1.12–1.39 |

| Bulk (TLS 1.3, send and receive) | 16 KiB records | 10000-byte records |
|---|---:|---:|
| AES-128/256-GCM | 0.76–0.83 | 0.66–0.84 |
| ChaCha20-Poly1305 | 0.98–1.01 | 0.98–0.99 |

## Primitives, through the rustls traits (`provider-primitives`)

Nanoseconds per operation, median of three runs.

| | aws-lc-rs | verified-garbage | ratio |
|---|---:|---:|---:|
| X25519MLKEM768 client share | 21 000 | 43 000 | 2.0 |
| X25519MLKEM768 server (encaps + DH) | 49 500 | 71 700 | 1.4 |
| X25519MLKEM768 client finish | 42 300 | 50 300 | 1.2 |
| X25519 keygen | 8 700 | 26 700 | 3.1 |
| X25519 DH | 27 600 | 26 600 | 1.0 |
| secp256r1 keygen | 11 700 | 355 000 | 30 |
| secp256r1 server (keygen + DH) | 61 700 | 690 000 | 11 |
| secp384r1 server (keygen + DH) | 234 000 | 2 150 000 | 9.2 |
| ML-KEM-768 encaps / decaps | 16 500 / 17 800 | 21 000 / 26 700 | 1.3 / 1.5 |
| ECDSA P-256 sign / verify | 20 300 / 64 700 | 386 000 / 767 600 | 19 / 12 |
| ECDSA P-384 sign / verify | 91 800 / 242 000 | 1 075 000 / 2 027 000 | 12 / 8.4 |
| ECDSA P-521 sign / verify | 168 000 / 378 000 | 5 970 000 / 10 710 000 | 36 / 28 |
| Ed25519 sign / verify | 10 000 / 40 800 | 16 800 / 62 900 | 1.7 / 1.5 |
| RSA-2048 PSS sign / verify | 357 000 / 22 900 | 390 000 / 100 600 | 1.1 / 4.4 |
| RSA-3072 PSS sign / verify | 940 000 / 43 200 | 2 702 000 / 193 000 | 2.9 / 4.5 |
| RSA-4096 PSS sign / verify | 1 892 000 / 75 100 | 6 096 000 / 337 000 | 3.2 / 4.5 |
| AES-128-GCM seal 16 KiB record | 1 170 | 1 615 | 1.4 |
| AES-256-GCM seal 16 KiB record | 1 450 | 1 860 | 1.3 |
| ChaCha20-Poly1305 seal 16 KiB record | 9 130 | 7 050 | 0.77 |
| HKDF-SHA256 extract + expand | 470 | 850 | 1.8 |
| ticket encrypt / decrypt (200 B) | 1 210 / 530 | 570 / 270 | 0.47 / 0.50 |

Adding up each side's operations reproduces rustls-bench's handshake rates:
a TLS 1.3 P-256 client does a key exchange and three ECDSA verifications
(two certificates, one CertificateVerify), about 2.3 ms with
verified-garbage against 0.26 ms with aws-lc-rs, plus ~70 µs of rustls.

## Library-level (`aws-lc-rs` and `verified-garbage` APIs directly)

| | aws-lc-rs | verified-garbage | ratio |
|---|---:|---:|---:|
| RSA-2048 `PublicKey::new` (precomputes for `public_op`) | — | 9 000 | |
| RSA-2048 `rsa_pss::verify` | — | 74 000 | |
| RSA-2048 `PublicKey::public_op` (precomputed, ADX) | — | 22 700 | |
| RSA-2048 PSS verify (whole) | 23 900 | 99 700 | 4.2 |
| ChaCha20-Poly1305 seal 256 B / 768 B / 1024 B | 330 / 580 / 760 | 770 / 2 090 / 710 | 2.3 / 3.6 / 0.95 |
| AES-128-GCM seal 128 B / 384 B / 16 KiB | 115 / 137 / 1 180 | 144 / 236 / 1 500 | 1.3 / 1.7 / 1.27 |
