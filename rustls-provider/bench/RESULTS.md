# rustls benchmarks: verified-garbage vs aws-lc-rs

Measured 2026-10-06 with `bench/run.sh 5`: verified-garbage at 7cdac586 (main), rustls
91aebe5d, aws-lc-rs 1.18.1. Each benchmark ran on one core (`taskset -c 2`)
of a 2.1 GHz Intel Xeon with SHA-NI, AVX-512 (IFMA, VAES, VPCLMULQDQ) and
ADX, the same CPU class as the first run (verified-garbage 8532494). Throughput is noisy
on this VM (±10%), and RSA-3072/4096 signing with verified-garbage more so
(below). Differences under ~10% are not significant.

Every ratio in this file is verified-garbage's speed relative to aws-lc-rs's.
Below 1 is slower; 0.5 is half as fast. For throughput the ratio is
verified-garbage / aws-lc-rs; for times it is aws-lc-rs / verified-garbage.
Each rustls-bench ratio is the geometric mean over the row's cipher suites,
and a range spans TLS 1.2 and 1.3.

## rustls-bench (`--api buffered`, median of 5 runs)

| | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 0.71–0.77 | 0.99–1.00 | 0.72–0.80 | 0.74–0.82 | 0.97–1.08 | 1.09–1.28 |
| ECDSA P-384 (TLS 1.2 only) | 0.48 | 0.83 | 0.51 | 0.52 | | 1.16–1.37 |
| RSA-2048 | 0.91–0.96 | 1.02–1.05 | 1.00–1.07 | 1.02–1.07 | 0.94–1.09 | 1.14–1.56 |
| Ed25519 | 1.14–1.22 | 1.01–1.04 | 1.13–1.21 | 1.14–1.22 | 0.98–1.06 | 1.17–1.37 |

| Bulk (TLS 1.3, send and receive) | 16 KiB records | 10000-byte records |
|---|---:|---:|
| AES-128/256-GCM | 0.85–0.95 | 0.73–0.91 |
| ChaCha20-Poly1305 | 1.30–1.31 | 1.11–1.15 |

## Primitives, through the rustls traits (`provider-primitives`)

Nanoseconds per operation, median of three runs; speed as above.

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| X25519MLKEM768 client share | 21 600 | 25 600 | 0.84 |
| X25519MLKEM768 server (encaps + DH) | 49 000 | 51 800 | 0.95 |
| X25519MLKEM768 client finish | 43 200 | 46 100 | 0.94 |
| X25519 keygen / DH | 8 300 / 25 100 | 6 900 / 24 700 | 1.21 / 1.01 |
| secp256r1 keygen / server (keygen + DH) | 11 100 / 59 500 | 13 500 / 92 400 | 0.82 / 0.64 |
| secp384r1 keygen / server (keygen + DH) | 53 300 / 209 300 | 54 900 / 419 200 | 0.97 / 0.50 |
| ML-KEM-768 keygen / encaps / decaps | 14 000 / 14 700 / 17 600 | 15 800 / 19 700 / 22 700 | 0.89 / 0.75 / 0.78 |
| ECDSA P-256 sign / verify | 18 900 / 61 000 | 18 400 / 91 500 | 1.03 / 0.67 |
| ECDSA P-384 sign / verify | 84 600 / 210 700 | 104 200 / 450 300 | 0.81 / 0.47 |
| ECDSA P-521 sign / verify | 159 700 / 329 700 | 280 800 / 1 047 400 | 0.57 / 0.31 |
| Ed25519 sign / verify | 9 100 / 37 400 | 8 600 / 26 100 | 1.06 / 1.43 |
| RSA-2048 PSS sign / verify | 341 500 / 20 100 | 364 000 / 28 300 | 0.94 / 0.71 |
| RSA-3072 PSS sign / verify | 1 073 300 / 44 100 | 1 516 900 / 59 600 | 0.71 / 0.74 |
| RSA-4096 PSS sign / verify | 2 084 900 / 72 700 | 2 428 500 / 101 200 | 0.86 / 0.72 |
| RSA-2048 / 3072 / 4096 load key | 181 400 / 353 800 / 613 300 | 395 400 / 1 319 100 / 2 455 100 | 0.46 / 0.27 / 0.25 |
| AES-128-GCM seal / open 16 KiB record | 1 280 / 1 350 | 1 510 / 1 440 | 0.85 / 0.93 |
| AES-256-GCM seal / open 16 KiB record | 1 410 / 1 500 | 1 640 / 1 570 | 0.86 / 0.95 |
| ChaCha20-Poly1305 seal / open 16 KiB record | 8 290 / 8 310 | 6 910 / 7 010 | 1.20 / 1.18 |
| HKDF-SHA256 / SHA384 extract + expand | 410 / 1 150 | 710 / 2 130 | 0.58 / 0.54 |
| transcript hash, SHA-256 / SHA-384 | 1 730 / 4 390 | 1 810 / 4 240 | 0.96 / 1.03 |
| ticket encrypt / decrypt (200 B) | 1 130 / 470 | 540 / 250 | 2.11 / 1.92 |

RSA-3072/4096 signing with verified-garbage varied from run to run: from 1.0
to 1.7 ms for 3072-bit keys, against aws-lc-rs's steady ~1.05 ms, so its speed
ranges from 0.6 to 1.1. RSA-2048 signing was steady.

Adding up each side's operations still accounts for rustls-bench's handshake
rates. For example, a TLS 1.3 P-256 client does an X25519MLKEM768 exchange
and three ECDSA verifications: about 0.35 ms with verified-garbage against
0.25 ms with aws-lc-rs.

## Library-level (`bench/aws-lc-compare`: each library's own API)

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| P-256 keygen / ECDH / sign / verify | 11 000 / 56 200 / 18 800 / 63 200 | 13 100 / 78 200 / 17 300 / 87 300 | 0.84 / 0.72 / 1.09 / 0.72 |
| X25519 keygen / DH | 8 100 / 33 000 | 6 500 / 22 100 | 1.25 / 1.49 |
| RSA-2048 PSS verify (whole) | 20 400 | 28 700 | 0.71 |
| — vg `PublicKey::new` (precomputes for verification) | | 7 900 | |
| — vg `rsa_pss::verify` (with those values) | | 20 200 | 1.01 |
| RSA-2048 / 3072 / 4096 PSS sign | 333 100 / 1 038 600 / 2 115 000 | 369 300 / 1 059 600 / 2 058 900 | 0.90 / 0.98 / 1.03 |
| RSA-2048 / 3072 / 4096 load private key | 156 600 / 312 000 / 706 600 | 334 300 / 1 035 500 / 1 889 400 | 0.47 / 0.30 / 0.37 |
| AES-128-GCM seal 128 B / 384 B / 1 KiB / 16 KiB | 102 / 117 / 174 / 1 200 | 131 / 178 / 159 / 1 310 | 0.78 / 0.66 / 1.09 / 0.92 |
| ChaCha20-Poly1305 seal 64 B / 256 B / 640 B / 1 KiB / 16 KiB | 199 / 305 / 495 / 696 / 7 810 | 226 / 317 / 602 / 705 / 6 610 | 0.88 / 0.96 / 0.82 / 0.99 / 1.18 |
| memcpy of a 16 KiB record (the provider's copy before sealing) | 123 | 123 | |

## Where the gaps are now

Speeds relative to aws-lc-rs, as above.

1. **P-384 and P-521 verification and ECDH: 0.31–0.50.** P-521 verification is
   0.31 and signing 0.57, up from 0.04–0.05 (#1040, #1047, #1064, #1067).
   P-384 verification and ECDH are 0.43–0.50, while P-384 signing (0.81) and
   key generation (0.97) are close. The P-384 rows are why TLS 1.2 P-384
   handshakes run at 0.48–0.83.
2. **P-256 verification and ECDH: 0.64–0.72.** Signing (1.03) and key
   generation (0.82) are close. This is what keeps P-256 client handshakes at
   0.71–0.77, since a client verifies three signatures.
3. **RSA verification: 0.71–0.74.** `rsa_pss::verify` with its precomputed
   values now matches aws-lc (1.01). The provider has to build a
   `PublicKey` from the certificate's bytes for every verification, though,
   and `PublicKey::new` takes ~8 µs (40% of aws-lc's whole verification) to
   precompute the Montgomery values.
4. **Loading an RSA private key: 0.25–0.47.** `PrivateKey::from_crt` checks
   the key with a full private-key operation. This is once per key, not per
   handshake.
5. **ML-KEM-768 encapsulation/decapsulation: 0.75–0.78**, which X25519MLKEM768
   dilutes to 0.84–0.95.
6. **AES-GCM: 0.85–0.95 for full records**, 0.66–0.78 for lengths of 128, 192
   and 384 bytes, and the copy before in-place sealing (#990).
7. **HKDF: 0.54–0.58**, from the provider using rustls's generic HMAC-based
   HKDF (about 0.3–1 µs per handshake). aws-lc-rs defers the extract to the
   expand, so compare the two together.

Faster than aws-lc-rs: Ed25519 verification (1.43), X25519 (1.0–1.5),
ChaCha20-Poly1305 records (1.18–1.20), and tickets (about 2).

## Changes since the first run

Speed relative to aws-lc-rs, by the verified-garbage commit each run measured.
The 8532494 and 7cdac586 runs share a CPU class; the 36ff93f9 run's CPU lacked
SHA-NI, IFMA, VAES and VPCLMULQDQ.

| | 8532494 (first run) | 36ff93f9 | 7cdac586 (now) |
|---|---:|---:|---:|
| P-256 full handshake, client / server | 0.11–0.15 / 0.16–0.24 | 0.52–0.60 / 0.74–0.91 | 0.71–0.77 / 0.99–1.00 |
| RSA-2048 full handshake, client / server | 0.42–0.47 / 0.93 | 0.48–0.55 / 0.58–0.59 | 0.91–0.96 / 1.02–1.05 |
| Ed25519 full handshake, client / server | 0.73–0.74 / 0.78–0.83 | 0.64–0.73 / 0.76–0.91 | 1.14–1.22 / 1.01–1.04 |
| Bulk AES-GCM / ChaCha20-Poly1305 (16 KiB) | 0.76–0.83 / 0.98–1.01 | 0.88–0.93 / 1.37–1.39 | 0.85–0.95 / 1.30–1.31 |
| ECDSA P-256 sign / verify | 0.05 / 0.08 | 0.56 / 0.44 | 1.03 / 0.67 |
| ECDSA P-521 sign / verify | 0.03 / 0.04 | 0.04 / 0.05 | 0.57 / 0.31 |
| RSA-2048 PSS verify | 0.23 | 0.25 | 0.71 |
| Ed25519 sign / verify | 0.60 / 0.65 | 0.55 / 0.57 | 1.06 / 1.43 |
| X25519 keygen | 0.33 | 0.54 | 1.21 |
