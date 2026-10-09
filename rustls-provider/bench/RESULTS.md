# rustls benchmarks: verified-garbage vs aws-lc-rs

The latest run, in detail: main at a70d41fa, measured with `bench/run.sh 5`
on a 2.1 GHz Intel Xeon with SHA-NI, AVX-512 (IFMA, VAES, VPCLMULQDQ) and
ADX, the CPU class of the first run (verified-garbage 8532494), with rustls
91aebe5d and aws-lc-rs 1.18.1, each benchmark on one core (`taskset -c 2`).
Throughput on these VMs moves by ±10% at best, so treat differences under
~10% as noise. Earlier runs are summarized at the end.

Every ratio in this file is verified-garbage's speed relative to aws-lc-rs's:
below 1 is slower, and 0.5 is half as fast. For throughput it is
verified-garbage / aws-lc-rs; for times, aws-lc-rs / verified-garbage. Each
rustls-bench ratio is the geometric mean over the row's cipher suites; a
range spans TLS 1.2 and 1.3.

Since the previous runs, main gained faster AES-GCM out-of-place encryption
(#1350, #1374, #1404, #1410), a stitched AVX2 ChaCha20-Poly1305 seal
(#1392), cheaper RSA key loading (#1343, #1355, #1403) and private-key
operations (#1357, #1385, #1395), and faster Ed25519/X25519 (#1351, #1358,
#1360, #1377, #1398). The provider now seals every record of both AEADs out
of place, at every length: `AesGcm::encrypt` and
`ChaCha20Poly1305::encrypt` read the payload's chunks and the content type
byte where they are and write only the record. Only a payload of 64 chunks or
more is still copied first.

## rustls-bench (`--api buffered`, median of 5 runs)

Every handshake is faster than aws-lc-rs's:

| | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 1.23–1.28 | 1.15–1.26 | 1.30–1.34 | 1.30–1.33 | 1.13–1.22 | 1.05–1.32 |
| ECDSA P-384 (TLS 1.2 only) | 1.23 | 1.44 | 1.26 | 1.24 | | 1.04–1.41 |
| RSA-2048 | 1.07–1.11 | 1.05–1.07 | 1.05–1.12 | 1.06–1.12 | 1.14–1.26 | 1.05–1.42 |
| Ed25519 | 1.28–1.62 | 1.16–1.38 | 1.24–1.34 | 1.23–1.31 | 1.13–1.24 | 1.08–1.37 |

| Bulk, send and receive | 16 KiB records | 10000-byte records |
|---|---:|---:|
| TLS 1.3 AES-128/256-GCM | 0.96–1.02 | 0.92–1.01 |
| TLS 1.3 ChaCha20-Poly1305 | 1.32–1.36 | 1.18–1.24 |
| TLS 1.2 AES-128/256-GCM | 0.94–1.16 | 0.99–1.06 |
| TLS 1.2 ChaCha20-Poly1305 | 1.32–1.37 | 1.24–1.36 |

## Primitives, through the rustls traits (`provider-primitives`)

Nanoseconds per operation, median of three runs; speed as above.

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| X25519MLKEM768 client share | 24 700 | 23 600 | 1.04 |
| X25519MLKEM768 server (encaps + DH) | 55 300 | 47 000 | 1.18 |
| X25519MLKEM768 client finish | 50 800 | 41 500 | 1.22 |
| X25519 keygen / server (keygen + DH) / DH | 9 200 / 37 400 / 28 500 | 7 100 / 31 500 / 28 500 | 1.29 / 1.19 / 1.00 |
| secp256r1 keygen / server / DH | 12 600 / 92 400 / 62 100 | 13 300 / 66 400 / 48 900 | 0.95 / 1.39 / 1.27 |
| secp384r1 keygen / server / DH | 62 600 / 241 500 / 172 700 | 38 800 / 215 100 / 185 200 | 1.61 / 1.12 / 0.93 |
| ML-KEM-768 keygen / encaps / decaps | 17 200 / 17 400 / 19 000 | 15 000 / 15 500 / 17 400 | 1.15 / 1.12 / 1.09 |
| ECDSA P-256 sign / verify | 20 900 / 68 800 | 16 200 / 56 600 | 1.30 / 1.22 |
| ECDSA P-384 sign / verify | 95 100 / 231 500 | 51 400 / 216 400 | 1.85 / 1.07 |
| ECDSA P-521 sign / verify | 184 000 / 415 500 | 96 100 / 339 700 | 1.91 / 1.22 |
| Ed25519 sign / verify | 11 000 / 46 900 | 8 400 / 28 300 | 1.31 / 1.66 |
| RSA-2048 PSS sign / verify | 461 200 / 23 400 | 352 400 / 25 000 | 1.31 / 0.94 |
| RSA-3072 PSS sign / verify | 1 146 200 / 48 200 | 1 077 500 / 50 700 | 1.06 / 0.95 |
| RSA-4096 PSS sign / verify | 2 078 800 / 81 900 | 2 011 600 / 87 500 | 1.03 / 0.94 |
| RSA-2048 / 3072 / 4096 load key | 219 700 / 412 300 / 670 800 | 57 400 / 107 700 / 178 300 | 3.83 / 3.83 / 3.76 |
| ECDSA P-256 / P-384 / P-521 load key | 26 000 / 221 600 / 387 000 | 15 000 / 41 600 / 81 100 | 1.74 / 5.32 / 4.77 |
| Ed25519 load key | 47 800 | 8 700 | 5.49 |
| AES-128-GCM seal / open 16 KiB record | 1 312 / 1 498 | 1 274 / 1 375 | 1.03 / 1.09 |
| AES-256-GCM seal / open 16 KiB record | 1 540 / 1 805 | 1 456 / 1 556 | 1.06 / 1.16 |
| AES-128-GCM seal / open 1 KiB record | 225 / 244 | 191 / 222 | 1.18 / 1.10 |
| AES-256-GCM seal / open 1 KiB record | 265 / 260 | 209 / 235 | 1.27 / 1.11 |
| ChaCha20-Poly1305 seal / open 16 KiB record | 9 354 / 9 491 | 7 229 / 7 294 | 1.29 / 1.30 |
| ChaCha20-Poly1305 seal / open 1 KiB record | 965 / 807 | 866 / 922 | 1.11 / 0.88 |
| HKDF-SHA256 / SHA384 extract + one expand | 812 / 2 690 | 808 / 2 420 | 1.00 / 1.11 |
| HKDF-SHA256 / SHA384 expand (one block) | 374 / 1 225 | 239 / 695 | 1.56 / 1.76 |
| transcript hash, SHA-256 / SHA-384 | 1 932 / 5 036 | 2 035 / 4 706 | 0.95 / 1.07 |
| ticket encrypt / decrypt (200 B) | 1 376 / 540 | 556 / 210 | 2.47 / 2.57 |

The open rows include copying the record into the buffer it is decrypted in.
aws-lc-rs defers HKDF's extract to the first expand, so an extract is timed
together with one expand of its result; previous runs timed the extract
alone, which made it look about half as fast.

## Library-level (`bench/aws-lc-compare`: each library's own API)

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| AES-128-GCM `encrypt_in_place` 128 B / 1 KiB / 16 KiB | 117 / 203 / 1 359 | 81 / 191 / 1 235 | 1.44 / 1.06 / 1.10 |
| AES-128-GCM `encrypt`, 2 pieces, 128+1 B / 1024+1 B / 16384+1 B | 123 / 216 / 1 310 | 110 / 180 / 1 219 | 1.12 / 1.20 / 1.07 |
| ChaCha20-Poly1305 seal 64 B / 256 B / 1 KiB / 16 KiB | 223 / 335 / 790 / 9 672 | 217 / 349 / 709 / 8 073 | 1.03 / 0.96 / 1.11 / 1.20 |
| P-256 keygen / ECDH / sign / verify | 12 500 / 76 700 / 23 800 / 74 600 | 12 900 / 62 300 / 16 700 / 55 800 | 0.96 / 1.23 / 1.43 / 1.34 |
| X25519 keygen / DH | 9 600 / 37 900 | 7 400 / 26 800 | 1.30 / 1.41 |
| RSA-2048 / 3072 / 4096 PSS sign | 365 300 / 1 025 200 / 2 158 900 | 364 800 / 1 102 500 / 2 056 200 | 1.00 / 0.93 / 1.05 |
| RSA-2048 / 3072 / 4096 PSS verify, from the key's bytes | 23 600 / 48 700 / 78 500 | 24 400 / 52 800 / 90 200 | 0.96 / 0.92 / 0.87 |
| — the same with the key's values already computed | | 21 400 / 43 000 / 75 700 | 1.10 / 1.13 / 1.04 |
| RSA-2048 / 3072 / 4096 load private key | 162 600 / 340 500 / 524 300 | 48 400 / 97 600 / 165 200 | 3.36 / 3.49 / 3.17 |
| HMAC-SHA256 / SHA384, 32 B | 468 / 1 298 | 339 / 1 135 | 1.38 / 1.14 |
| HKDF-SHA256 / SHA384 extract + expand | 807 / 2 494 | 666 / 2 370 | 1.21 / 1.05 |

The out-of-place rows time `AesGcm::encrypt` with the payload and a content
type byte in two pieces, as the provider calls it, against aws-lc-rs sealing
as many bytes in place. On this CPU it is now at least as fast as
copying and `encrypt_in_place` from 256 bytes, and 10–14 ns slower below;
`ChaCha20Poly1305::encrypt` is 3–7% slower than copying and
`encrypt_in_place` from 1 KiB. Sub-jobs are removing both costs in the
library's assembly.

## Remaining gaps

1. **RSA verification from a certificate's key: 0.87–0.96.** With the key's
   Montgomery values already computed, verification is 1.04–1.13; computing
   them on a new key's first use costs the difference, and the provider
   verifies each certificate with a new key.
2. **ChaCha20-Poly1305 opening a 1 KiB record: 0.88**, and sealing 256 B,
   0.85–0.96. Decryption runs ChaCha20 and Poly1305 one after the other.
3. **P-384 ECDH, [k]P alone: 0.93.** Key generation (1.61) and the server's
   whole exchange (1.12) are faster.
4. **Bulk AES-GCM receive in TLS 1.3: 0.92–0.97**, while opening a record
   alone is 1.09–1.16, so likely noise.
5. **P-256 key generation (0.95–0.96) and the SHA-256 transcript hash
   (0.95)**, within noise.

The last run on a CPU without IFMA, VAES or SHA-NI (b5b67857, in the table below) had
larger gaps there: RSA private-key operations, Ed25519 signing and short
ChaCha20-Poly1305 messages. Those have since been worked on, but this CPU
can't measure them.

## Changes since the first run

Speed relative to aws-lc-rs, by the verified-garbage commit each run measured.
The 8532494, 7cdac586, 93f54441 and a70d41fa runs share a CPU class; the
36ff93f9 and b5b67857 runs' CPU lacked SHA-NI, IFMA, VAES and VPCLMULQDQ,
and the b5b67857 run's host was noisy. The provider sealed every record with
a copy before 93f54441, and short AES-GCM records and every
ChaCha20-Poly1305 record until a70d41fa.

| | 8532494 (first run) | 36ff93f9 | 7cdac586 | 93f54441 | b5b67857 (noisy) | a70d41fa |
|---|---:|---:|---:|---:|---:|---:|
| P-256 full handshake, client / server | 0.11–0.15 / 0.16–0.24 | 0.52–0.60 / 0.74–0.91 | 0.71–0.77 / 0.99–1.00 | 1.25–1.27 / 1.20–1.23 | 0.90–1.27 / 0.80–1.22 | 1.23–1.28 / 1.15–1.26 |
| RSA-2048 full handshake, client / server | 0.42–0.47 / 0.93 | 0.48–0.55 / 0.58–0.59 | 0.91–0.96 / 1.02–1.05 | 1.06 / 1.08 | 0.84–1.03 / 0.71–0.86 | 1.07–1.11 / 1.05–1.07 |
| Ed25519 full handshake, client / server | 0.73–0.74 / 0.78–0.83 | 0.64–0.73 / 0.76–0.91 | 1.14–1.22 / 1.01–1.04 | 1.26–1.29 / 1.08–1.13 | 1.18–1.21 / 1.02–1.10 | 1.28–1.62 / 1.16–1.38 |
| Bulk AES-GCM / ChaCha20-Poly1305 (16 KiB) | 0.76–0.83 / 0.98–1.01 | 0.88–0.93 / 1.37–1.39 | 0.85–0.95 / 1.30–1.31 | 0.89–0.94 / 1.24–1.27 | 0.72–1.01 / 1.08–1.09 | 0.96–1.02 / 1.32–1.36 |
| AES-128/256-GCM 16 KiB record seal | 0.72 / 0.78 | 0.88 / 0.86 | 0.85 / 0.86 | 0.97 / 1.02 | 0.79 / 0.80 | 1.03 / 1.06 |
| ECDSA P-256 sign / verify | 0.05 / 0.08 | 0.56 / 0.44 | 1.03 / 0.67 | 1.27 / 1.24 | 1.01 / 1.13 | 1.30 / 1.22 |
| ECDSA P-521 sign / verify | 0.03 / 0.04 | 0.04 / 0.05 | 0.57 / 0.31 | 1.77 / 1.05 | 2.04 / 1.28 | 1.91 / 1.22 |
| RSA-2048 PSS verify | 0.23 | 0.25 | 0.71 | 0.83 | 0.94 | 0.94 |
| Ed25519 sign / verify | 0.60 / 0.65 | 0.55 / 0.57 | 1.06 / 1.43 | 1.18 / 1.57 | 0.79 / 1.28 | 1.31 / 1.66 |
| X25519 keygen | 0.33 | 0.54 | 1.21 | 1.29 | 0.82 | 1.29 |
