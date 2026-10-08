# rustls benchmarks: verified-garbage vs aws-lc-rs

Measured 2026-10-08 with `bench/run.sh 5`: verified-garbage at 93f54441
(main) with the provider sealing AES-GCM records out of place, rustls
91aebe5d, aws-lc-rs 1.18.1. Each benchmark ran on one core (`taskset -c 2`)
of a 2.1 GHz Intel Xeon with SHA-NI, AVX-512 (IFMA, VAES, VPCLMULQDQ) and
ADX, the CPU class of the first run (verified-garbage 8532494). Throughput is
noisy on this VM (±10%), and RSA-3072/4096 signing with verified-garbage more
so, so treat differences under ~10% as noise.

Every ratio in this file is verified-garbage's speed relative to aws-lc-rs's:
below 1 is slower, and 0.5 is half as fast. For throughput it is
verified-garbage / aws-lc-rs; for times, aws-lc-rs / verified-garbage. Each
rustls-bench ratio is the geometric mean over the row's cipher suites; a
range spans TLS 1.2 and 1.3.

## rustls-bench (`--api buffered`, median of 5 runs)

| | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 1.25–1.27 | 1.20–1.23 | 1.23–1.28 | 1.21–1.28 | 1.14–1.26 | 1.10–1.33 |
| ECDSA P-384 (TLS 1.2 only) | 1.10 | 1.38 | 1.18 | 1.20 | | 1.08–1.31 |
| RSA-2048 | 1.06 | 1.08 | 1.06–1.08 | 1.05–1.07 | 1.11–1.29 | 1.04–1.43 |
| Ed25519 | 1.26–1.29 | 1.08–1.13 | 1.30–1.34 | 1.27–1.31 | 1.13–1.24 | 1.07–1.26 |

| Bulk (TLS 1.3, send and receive) | 16 KiB records | 10000-byte records |
|---|---:|---:|
| AES-128/256-GCM | 0.89–0.94 | 0.87–0.94 |
| ChaCha20-Poly1305 | 1.24–1.27 | 1.24–1.28 |

## Primitives, through the rustls traits (`provider-primitives`)

Nanoseconds per operation, median of three runs; speed as above.

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| X25519MLKEM768 client share | 22 700 | 20 000 | 1.14 |
| X25519MLKEM768 server (encaps + DH) | 49 700 | 42 900 | 1.16 |
| X25519MLKEM768 client finish | 44 900 | 41 700 | 1.08 |
| X25519 keygen / DH | 9 000 / 27 100 | 6 900 / 23 400 | 1.29 / 1.16 |
| secp256r1 keygen / server (keygen + DH) | 11 700 / 60 900 | 11 000 / 58 900 | 1.07 / 1.03 |
| secp384r1 keygen / server (keygen + DH) | 53 500 / 206 200 | 39 800 / 267 700 | 1.34 / 0.77 |
| ML-KEM-768 keygen / encaps / decaps | 13 900 / 14 300 / 18 600 | 14 700 / 15 100 / 15 500 | 0.94 / 0.95 / 1.20 |
| ECDSA P-256 sign / verify | 18 100 / 60 700 | 14 200 / 48 800 | 1.27 / 1.24 |
| ECDSA P-384 sign / verify | 81 900 / 208 000 | 50 300 / 191 300 | 1.63 / 1.09 |
| ECDSA P-521 sign / verify | 172 800 / 355 200 | 97 400 / 338 300 | 1.77 / 1.05 |
| Ed25519 sign / verify | 9 400 / 38 800 | 7 900 / 24 700 | 1.18 / 1.57 |
| RSA-2048 PSS sign / verify | 337 500 / 21 700 | 332 900 / 26 000 | 1.01 / 0.83 |
| RSA-3072 PSS sign / verify | 886 100 / 43 700 | 1 075 500 / 55 900 | 0.82 / 0.78 |
| RSA-4096 PSS sign / verify | 1 844 200 / 73 400 | 1 968 200 / 103 700 | 0.94 / 0.71 |
| RSA-2048 / 3072 / 4096 load key | 167 500 / 307 600 / 535 700 | 349 800 / 1 132 900 / 1 846 900 | 0.48 / 0.27 / 0.29 |
| AES-128-GCM seal / open 16 KiB record | 1 140 / 1 240 | 1 170 / 1 250 | 0.97 / 1.00 |
| AES-256-GCM seal / open 16 KiB record | 1 440 / 1 450 | 1 420 / 1 470 | 1.02 / 0.99 |
| AES-128-GCM seal / open 1 KiB record | 208 / 234 | 229 / 189 | 0.91 / 1.24 |
| AES-256-GCM seal / open 1 KiB record | 236 / 234 | 241 / 204 | 0.98 / 1.15 |
| ChaCha20-Poly1305 seal / open 16 KiB record | 8 560 / 8 610 | 6 700 / 6 590 | 1.28 / 1.31 |
| ChaCha20-Poly1305 seal / open 1 KiB record | 888 / 713 | 784 / 773 | 1.13 / 0.92 |
| HKDF-SHA256 / SHA384 extract + expand | 420 / 1 200 | 740 / 2 240 | 0.57 / 0.54 |
| transcript hash, SHA-256 / SHA-384 | 1 690 / 4 770 | 1 780 / 4 230 | 0.95 / 1.13 |
| ticket encrypt / decrypt (200 B) | 1 110 / 475 | 490 / 184 | 2.28 / 2.58 |

## Library-level (`bench/aws-lc-compare`: each library's own API)

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| P-256 keygen / ECDH / sign / verify | 11 700 / 60 000 / 20 800 / 65 300 | 10 700 / 46 900 / 14 900 / 50 500 | 1.10 / 1.28 / 1.40 / 1.29 |
| X25519 keygen / DH | 8 800 / 33 400 | 5 700 / 22 900 | 1.54 / 1.46 |
| RSA-2048 PSS verify (whole) | 21 300 | 25 600 | 0.83 |
| — vg `PublicKey::new` (precomputes for verification) | | 7 500 | |
| — vg `rsa_pss::verify` (with those values) | | 17 900 | 1.19 |
| RSA-2048 / 3072 / 4096 PSS sign | 339 100 / 900 200 / 1 798 700 | 359 700 / 964 300 / 1 818 500 | 0.94 / 0.93 / 0.99 |
| AES-128-GCM `encrypt_in_place` 128 B / 1 KiB / 16 KiB | 100 / 179 / 1 129 | 73 / 163 / 1 118 | 1.37 / 1.10 / 1.01 |
| AES-128-GCM `encrypt`, 2 pieces, 128+1 B / 1024+1 B / 16384+1 B | 112 / 176 / 1 108 | 151 / 198 / 1 216 | 0.74 / 0.89 / 0.91 |
| ChaCha20-Poly1305 seal 64 B / 256 B / 1 KiB / 16 KiB | 215 / 315 / 707 / 9 030 | 212 / 338 / 710 / 6 890 | 1.01 / 0.93 / 1.00 |

The out-of-place rows time verified-garbage's `AesGcm::encrypt` with the
payload and a content type byte in two pieces, as the provider calls it,
against aws-lc-rs sealing as many bytes in place.

## AES-GCM records out of place

The provider seals an AES-GCM record with `AesGcm::encrypt` (#1228). It reads
the payload's chunks and, for TLS 1.3, the content type byte where they are,
and writes only the record, so there is no copy into it first. ChaCha20-Poly1305
has the contracts (#1209) but no implementation yet, so it still copies and
encrypts in place.

Measured in one process on this CPU, against copying and `encrypt_in_place`:

* **Under 512 bytes, `encrypt` takes about twice as long** (16 B: 113 against
  65 ns). It has no path for short inputs, and `encrypt_in_place` has
  (#1162, #1170). The provider therefore copies and encrypts in place below
  512 bytes.
* **From 512 bytes to 4 KiB they are within noise; at 8 KiB `encrypt` is
  ahead** (AES-128: 897 against 1 053 ns).
* **At 16 KiB, `encrypt` saves the copy (~130 ns), but its loop is 5–10%
  slower than `encrypt_in_place`'s** (16384+1 B in two pieces: 0.91 of
  aws-lc-rs's speed, against 1.01 in place). Records end up at 0.97–1.02,
  up from 0.85–0.88 with the copy.
* **Initializing an array of 64 pieces per record cost 25–45 ns**, about a
  sixth of a 1 KiB record, so a record in one chunk (the usual case) passes
  its two pieces directly.

## Where the gaps are now

Speeds relative to aws-lc-rs, as above.

1. **RSA verification: 0.71–0.83.** `rsa_pss::verify` with its precomputed
   values is faster than aws-lc (1.09–1.19). The provider still builds a
   `PublicKey` from the certificate's bytes for every verification, and
   `PublicKey::new` takes 7.5–31 µs to precompute the Montgomery values.
2. **P-384 ECDH: 0.68–0.77.** P-384 key generation (1.34), signing (1.63) and
   verification (1.09) are faster than aws-lc.
3. **Loading an RSA private key: 0.27–0.48.** `PrivateKey::from_crt` checks
   the key with a full private-key operation. This is once per key, not per
   handshake.
4. **Bulk AES-GCM: 0.87–0.94** through rustls-bench. 16 KiB record seal and
   open alone are at 0.97–1.02, and 1 KiB seals at 0.91–0.98. The library's `AesGcm::encrypt` is the open item:
   it has no short-input path and its 16 KiB loop is 5–10% behind
   `encrypt_in_place`.
5. **RSA-3072 signing: 0.82–0.93**, and unstable from run to run (1.0–1.7 ms
   in earlier runs).
6. **HKDF: 0.54–0.57**, from the provider using rustls's generic HMAC-based
   HKDF (about 0.3–1 µs per handshake). aws-lc-rs defers the extract to the
   expand, so the two are compared together.

Everything else is at parity or faster: every rustls-bench handshake
(1.04–1.43), P-256 (1.02–1.27), P-521 (1.05–1.77), Ed25519 (1.18–1.57),
X25519 (1.16–1.29), ChaCha20-Poly1305 records (1.28–1.31), and tickets
(about 2.4).

## Changes since the first run

Speed relative to aws-lc-rs, by the verified-garbage commit each run measured.
The 8532494, 7cdac586 and 93f54441 runs share a CPU class; the 36ff93f9 run's
CPU lacked SHA-NI, IFMA, VAES and VPCLMULQDQ. The provider sealed every
record with a copy before 93f54441.

| | 8532494 (first run) | 36ff93f9 | 7cdac586 | 93f54441 (now) |
|---|---:|---:|---:|---:|
| P-256 full handshake, client / server | 0.11–0.15 / 0.16–0.24 | 0.52–0.60 / 0.74–0.91 | 0.71–0.77 / 0.99–1.00 | 1.25–1.27 / 1.20–1.23 |
| RSA-2048 full handshake, client / server | 0.42–0.47 / 0.93 | 0.48–0.55 / 0.58–0.59 | 0.91–0.96 / 1.02–1.05 | 1.06 / 1.08 |
| Ed25519 full handshake, client / server | 0.73–0.74 / 0.78–0.83 | 0.64–0.73 / 0.76–0.91 | 1.14–1.22 / 1.01–1.04 | 1.26–1.29 / 1.08–1.13 |
| Bulk AES-GCM / ChaCha20-Poly1305 (16 KiB) | 0.76–0.83 / 0.98–1.01 | 0.88–0.93 / 1.37–1.39 | 0.85–0.95 / 1.30–1.31 | 0.89–0.94 / 1.24–1.27 |
| AES-128/256-GCM 16 KiB record seal | 0.72 / 0.78 | 0.88 / 0.86 | 0.85 / 0.86 | 0.97 / 1.02 |
| ECDSA P-256 sign / verify | 0.05 / 0.08 | 0.56 / 0.44 | 1.03 / 0.67 | 1.27 / 1.24 |
| ECDSA P-521 sign / verify | 0.03 / 0.04 | 0.04 / 0.05 | 0.57 / 0.31 | 1.77 / 1.05 |
| RSA-2048 PSS verify | 0.23 | 0.25 | 0.71 | 0.83 |
| Ed25519 sign / verify | 0.60 / 0.65 | 0.55 / 0.57 | 1.06 / 1.43 | 1.18 / 1.57 |
| X25519 keygen | 0.33 | 0.54 | 1.21 | 1.29 |
