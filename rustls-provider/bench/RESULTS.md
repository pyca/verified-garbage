# rustls benchmarks: verified-garbage vs aws-lc-rs

The latest run, in detail: main at 7c42c0e1, measured with `bench/run.sh 5`
on a 2.1 GHz Intel Xeon (Emerald Rapids) with SHA-NI, AVX-512 (IFMA, VAES,
VPCLMULQDQ) and ADX, with rustls 91aebe5d and aws-lc-rs 1.18.1, each
benchmark on one core (`taskset -c 2`). The a70d41fa run before it had the same
features but was an older core. Both libraries are faster here, aws-lc-rs's
ChaCha20-Poly1305 most of all, so compare ratios across runs, not times.
Throughput on these VMs moves by ±10% at best, so treat differences under
~10% as noise. Earlier runs are summarized at the end.

Every ratio in this file is verified-garbage's speed relative to aws-lc-rs's:
below 1 is slower, and 0.5 is half as fast. For throughput it is
verified-garbage / aws-lc-rs; for times, aws-lc-rs / verified-garbage. Each
rustls-bench ratio is the geometric mean over the row's cipher suites; a
range spans TLS 1.2 and 1.3.

Since a70d41fa, main gained:

* **AES-GCM:** unaligned pieces encrypted straight to the output (#1467), a
  piece's last 16 bytes copied at once (#1474), and AVX-512 sealing that
  ends without single-block calls (#1485).
* **ChaCha20-Poly1305:**
  * a faster copy in the out-of-place gather (#1468);
  * stitched AVX2 opening (#1476), with Poly1305 interleaved with the
    quarter rounds (#1484);
  * AVX2 tail passes for short messages (#1479, #1646);
  * no lone block for TLS 1.3's n·1024+1 lengths on AVX-512 (#1482).
* **RSA:** faster private-key operations (#1466), and a cheaper first
  verification with a new public key (#1475, #1481).
* **Ed25519/X25519:** #1421 and #1472.

The provider seals every record of both AEADs out of place, at every length:
`AesGcm::encrypt` and `ChaCha20Poly1305::encrypt` read the payload's chunks
and the content type byte where they are and write only the record. Only a
payload of 64 chunks or more is copied first.

## rustls-bench (`--api buffered`, median of 5 runs)

Every handshake is at least as fast as aws-lc-rs's:

| | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 1.10–1.37 | 1.04–1.29 | 1.22–1.31 | 1.21–1.32 | 1.02–1.15 | 1.13–1.40 |
| ECDSA P-384 (TLS 1.2 only) | 1.21 | 1.36 | 1.28 | 1.30 | | 1.15–1.40 |
| RSA-2048 | 1.19–1.22 | 1.12–1.15 | 1.01–1.20 | 1.01–1.20 | 1.03–1.19 | 1.11–1.47 |
| Ed25519 | 1.18–1.34 | 1.00–1.22 | 1.16–1.21 | 1.13–1.22 | 1.11–1.18 | 1.16–1.51 |

| Bulk, send and receive | 16 KiB records | 10000-byte records |
|---|---:|---:|
| TLS 1.3 AES-128/256-GCM | 1.02–1.05 | 0.99–1.10 |
| TLS 1.3 ChaCha20-Poly1305 | 1.09–1.18 | 1.10–1.17 |
| TLS 1.2 AES-128/256-GCM | 0.91–1.03 | 0.96–1.17 |
| TLS 1.2 ChaCha20-Poly1305 | 1.23–1.26 | 1.11–1.32 |

## Primitives, through the rustls traits (`provider-primitives`)

Nanoseconds per operation, median of three runs; speed as above.

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| X25519MLKEM768 client share | 22 600 | 20 900 | 1.08 |
| X25519MLKEM768 server (encaps + DH) | 47 400 | 45 800 | 1.04 |
| X25519MLKEM768 client finish | 40 200 | 37 000 | 1.09 |
| X25519 keygen / server (keygen + DH) / DH | 7 800 / 33 000 / 25 800 | 6 700 / 31 300 / 23 500 | 1.16 / 1.05 / 1.10 |
| secp256r1 keygen / server / DH | 11 000 / 60 600 / 46 700 | 10 700 / 58 500 / 46 900 | 1.03 / 1.04 / 1.00 |
| secp384r1 keygen / server / DH | 56 000 / 206 200 / 149 300 | 35 400 / 181 600 / 148 600 | 1.58 / 1.14 / 1.01 |
| ML-KEM-768 keygen / encaps / decaps | 14 000 / 14 900 / 17 800 | 13 300 / 14 100 / 14 000 | 1.05 / 1.06 / 1.27 |
| ECDSA P-256 sign / verify | 18 300 / 54 700 | 13 800 / 46 300 | 1.33 / 1.18 |
| ECDSA P-384 sign / verify | 84 900 / 195 000 | 42 100 / 156 700 | 2.02 / 1.24 |
| ECDSA P-521 sign / verify | 161 400 / 336 000 | 85 200 / 293 900 | 1.89 / 1.14 |
| Ed25519 sign / verify | 9 500 / 42 100 | 7 800 / 24 200 | 1.22 / 1.74 |
| RSA-2048 PSS sign / verify | 348 500 / 20 400 | 319 800 / 19 500 | 1.09 / 1.05 |
| RSA-3072 PSS sign / verify | 1 031 500 / 42 000 | 948 800 / 41 600 | 1.09 / 1.01 |
| RSA-4096 PSS sign / verify | 2 119 000 / 63 100 | 1 629 500 / 67 800 | 1.30 / 0.93 |
| RSA-2048 / 3072 / 4096 load key | 178 100 / 357 700 / 675 600 | 50 400 / 96 200 / 177 600 | 3.53 / 3.72 / 3.80 |
| ECDSA P-256 / P-384 / P-521 load key | 23 300 / 152 800 / 337 900 | 11 900 / 35 200 / 76 200 | 1.95 / 4.34 / 4.43 |
| Ed25519 load key | 42 100 | 7 500 | 5.60 |
| AES-128-GCM seal / open 16 KiB record | 1 188 / 1 326 | 1 059 / 1 037 | 1.12 / 1.28 |
| AES-256-GCM seal / open 16 KiB record | 1 390 / 1 509 | 1 254 / 1 442 | 1.11 / 1.05 |
| AES-128-GCM seal / open 1 KiB record | 210 / 217 | 176 / 189 | 1.19 / 1.15 |
| AES-256-GCM seal / open 1 KiB record | 226 / 227 | 191 / 205 | 1.18 / 1.11 |
| ChaCha20-Poly1305 seal / open 16 KiB record | 8 425 / 7 971 | 6 393 / 6 231 | 1.32 / 1.28 |
| ChaCha20-Poly1305 seal / open 1 KiB record | 863 / 708 | 645 / 712 | 1.34 / 0.99 |
| HKDF-SHA256 / SHA384 extract + one expand | 697 / 2 192 | 639 / 2 146 | 1.09 / 1.02 |
| HKDF-SHA256 / SHA384 expand (one block) | 329 / 1 101 | 198 / 558 | 1.66 / 1.97 |
| transcript hash, SHA-256 / SHA-384 | 1 713 / 4 364 | 1 680 / 4 041 | 1.02 / 1.08 |
| ticket encrypt / decrypt (200 B) | 1 149 / 468 | 478 / 165 | 2.40 / 2.84 |

The open rows include copying the record into the buffer it is decrypted in.
aws-lc-rs defers HKDF's extract to the first expand, so an extract is timed
together with one expand of its result. The HKDF rows are from a rerun after
the provider replaced rustls's generic `HkdfUsingHmac` with its own HKDF on
the library's HMAC (`src/hkdf.rs`), which allocates one box per extract
instead of three and a `Vec`. With `HkdfUsingHmac`, extract + expand was
704 / 1 967 ns (0.91 / 1.12); in one process the new one measured 18–25%
faster.

## Library-level (`bench/aws-lc-compare`: each library's own API)

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| AES-128-GCM `encrypt_in_place` 128 B / 1 KiB / 16 KiB | 100 / 167 / 1 201 | 68 / 143 / 957 | 1.47 / 1.17 / 1.25 |
| AES-128-GCM `encrypt`, 2 pieces, 128+1 B / 1024+1 B / 16384+1 B | 108 / 163 / 1 193 | 80 / 140 / 1 175 | 1.35 / 1.16 / 1.02 |
| ChaCha20-Poly1305 seal 64 B / 256 B / 512 B / 1 KiB / 16 KiB | 201 / 297 / 440 / 690 / 7 297 | 179 / 299 / 496 / 700 / 6 861 | 1.12 / 0.99 / 0.89 / 0.99 / 1.06 |
| P-256 keygen / ECDH / sign / verify | 10 300 / 51 000 / 17 700 / 55 900 | 10 400 / 47 400 / 11 900 / 41 800 | 1.00 / 1.08 / 1.48 / 1.34 |
| X25519 keygen / DH | 8 200 / 30 900 | 6 300 / 20 600 | 1.32 / 1.50 |
| RSA-2048 / 3072 / 4096 PSS sign | 331 800 / 1 025 900 / 2 025 300 | 310 100 / 851 700 / 1 856 400 | 1.07 / 1.20 / 1.09 |
| RSA-2048 / 3072 / 4096 PSS verify, from the key's bytes | 19 600 / 40 000 / 71 200 | 19 200 / 41 800 / 69 500 | 1.02 / 0.96 / 1.02 |
| — the same with the key's values already computed | | 17 800 / 36 500 / 64 000 | 1.10 / 1.10 / 1.11 |
| RSA-2048 / 3072 / 4096 load private key | 165 600 / 324 600 / 578 000 | 35 300 / 81 800 / 151 600 | 4.69 / 3.97 / 3.81 |
| HMAC-SHA256 / SHA384, 32 B | 398 / 1 040 | 291 / 944 | 1.37 / 1.10 |
| HKDF-SHA256 / SHA384 extract + expand | 678 / 2 152 | 597 / 1 967 | 1.14 / 1.09 |

The out-of-place rows time `AesGcm::encrypt` with the payload and a content
type byte in two pieces, as the provider calls it, against aws-lc-rs sealing
as many bytes in place.

## Remaining gaps

1. **ChaCha20-Poly1305 from 512 bytes to 1 KiB: 0.89–0.99** (in place: 512 B
   0.89, 640 B 0.90, 768 B 0.94), on this CPU's AVX-512 backend. Opening a
   1 KiB record is now 0.99, from 0.88 (#1482).
2. **RSA-4096 verification through the provider: 0.93**, with the
   library-level row at 1.02, so likely noise. RSA verification from a
   certificate's key is otherwise at 0.96–1.05, from 0.87–0.96.
3. **TLS 1.2 AES-256-GCM bulk: 0.91–0.97** in some scenarios, while the record
   seal and open alone are 1.05–1.11, so likely noise.

The last run on a CPU without IFMA, VAES or SHA-NI (b5b67857, in the table
below) had larger gaps there: RSA private-key operations, Ed25519 signing
and short ChaCha20-Poly1305 messages. Those have since been worked on, but
this CPU can't measure them.

## Cascade Lake class, emulated (7c42c0e1)

The same machine and commit with both libraries restricted to a Cascade Lake
class's features: AVX-512F/BW/VL, AVX2, BMI1/2, ADX, AES-NI, PCLMULQDQ and
SSSE3, but no AVX512-IFMA, VAES, VPCLMULQDQ or SHA-NI (`VG_CPU_FEATURES` and
`OPENSSL_ia32cap`, as `bench/run.sh` describes). Masking features does not
reproduce that core's microarchitecture, only the code paths each library
takes on it.

| rustls-bench | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 1.16–1.23 | 0.93–1.15 | 1.11–1.33 | 1.06–1.33 | 1.06–1.19 | 1.02–1.44 |
| ECDSA P-384 (TLS 1.2 only) | 1.16 | 1.23 | 1.26 | 1.26 | | 0.97–1.58 |
| RSA-2048 | 1.02–1.04 | 0.91–0.93 | 0.93–0.95 | 0.94 | 1.05–1.22 | 0.99–1.53 |
| Ed25519 | 1.05–1.11 | 0.95–1.08 | 1.06–1.08 | 1.05–1.06 | 1.00–1.17 | 1.07–1.47 |

| Bulk, send / receive | 16 KiB records | 10000-byte records |
|---|---:|---:|
| TLS 1.3 AES-128/256-GCM | 0.89–0.95 / 1.01–1.05 | 0.82–0.83 / 1.00–1.01 |
| TLS 1.3 ChaCha20-Poly1305 | 1.16 / 1.23 | 1.12 / 1.17 |
| TLS 1.2 AES-128/256-GCM | 0.88–0.94 / 0.99–1.05 | 0.84–0.86 / 1.03–1.06 |
| TLS 1.2 ChaCha20-Poly1305 | 1.23 / 1.23–1.24 | 1.14 / 1.18–1.20 |

The gaps on this class, by speed relative to aws-lc-rs:

1. **AES-GCM sealing, 256 bytes to 1 KiB and TLS-shaped lengths: 0.71–0.93.**
   In place, 384 B is 0.71–0.74 and 768 B 0.75; out of place (payload plus
   type byte), 256+1 to 1088+1 B is 0.72–0.93, and 4096+1 B 0.85 for
   AES-256. Records seal at 0.89–0.90 (1 KiB and 16 KiB), so bulk sending is
   0.82–0.95, while opening is 1.12–1.25. This is the AES-NI + AVX backend,
   which has no out-of-place interleaved loop.
2. **RSA private-key operations: 0.89–0.92** (PSS signing at 2048, 3072
   and 4096 bits), hence RSA server handshakes at 0.91–0.95.
3. **The SHA-256 transcript hash without SHA-NI: 0.86**, HKDF-SHA256 0.95–0.99.
   SHA-384 is 1.05–1.16.
4. **X25519 Diffie-Hellman: 0.94–0.95**, and the X25519MLKEM768 server's
   exchange 0.92. X25519 key generation is 1.11–1.14 and Ed25519 signing 1.21.
5. **ChaCha20-Poly1305 at 512 and 768 bytes: 0.86–0.88**, and opening a 1 KiB
   record 0.91 (the AVX-512 backend, as on the full CPU).

Faster than aws-lc-rs on this class: every ECDSA operation (1.09–2.12),
Ed25519 (1.21 / 1.28), P-384 key exchange, key loading (1.9–5.1),
ChaCha20-Poly1305 records (1.22–1.27 at 16 KiB), AES-GCM opening and
tickets.

## Changes since the first run

Speed relative to aws-lc-rs, by the verified-garbage commit each run measured.
The 8532494, 7cdac586, 93f54441, a70d41fa and 7c42c0e1 runs share a CPU class (7c42c0e1 on a newer core); the
36ff93f9 and b5b67857 runs' CPU lacked SHA-NI, IFMA, VAES and VPCLMULQDQ,
and the b5b67857 run's host was noisy. The provider sealed every record with
a copy before 93f54441, and short AES-GCM records and every
ChaCha20-Poly1305 record until a70d41fa.

| | 8532494 (first run) | 36ff93f9 | 7cdac586 | 93f54441 | b5b67857 (noisy) | a70d41fa | 7c42c0e1 |
|---|---:|---:|---:|---:|---:|---:|---:|
| P-256 full handshake, client / server | 0.11–0.15 / 0.16–0.24 | 0.52–0.60 / 0.74–0.91 | 0.71–0.77 / 0.99–1.00 | 1.25–1.27 / 1.20–1.23 | 0.90–1.27 / 0.80–1.22 | 1.23–1.28 / 1.15–1.26 | 1.10–1.37 / 1.04–1.29 |
| RSA-2048 full handshake, client / server | 0.42–0.47 / 0.93 | 0.48–0.55 / 0.58–0.59 | 0.91–0.96 / 1.02–1.05 | 1.06 / 1.08 | 0.84–1.03 / 0.71–0.86 | 1.07–1.11 / 1.05–1.07 | 1.19–1.22 / 1.12–1.15 |
| Ed25519 full handshake, client / server | 0.73–0.74 / 0.78–0.83 | 0.64–0.73 / 0.76–0.91 | 1.14–1.22 / 1.01–1.04 | 1.26–1.29 / 1.08–1.13 | 1.18–1.21 / 1.02–1.10 | 1.28–1.62 / 1.16–1.38 | 1.18–1.34 / 1.00–1.22 |
| Bulk AES-GCM / ChaCha20-Poly1305 (16 KiB) | 0.76–0.83 / 0.98–1.01 | 0.88–0.93 / 1.37–1.39 | 0.85–0.95 / 1.30–1.31 | 0.89–0.94 / 1.24–1.27 | 0.72–1.01 / 1.08–1.09 | 0.96–1.02 / 1.32–1.36 | 1.02–1.05 / 1.09–1.18 |
| AES-128/256-GCM 16 KiB record seal | 0.72 / 0.78 | 0.88 / 0.86 | 0.85 / 0.86 | 0.97 / 1.02 | 0.79 / 0.80 | 1.03 / 1.06 | 1.12 / 1.11 |
| ECDSA P-256 sign / verify | 0.05 / 0.08 | 0.56 / 0.44 | 1.03 / 0.67 | 1.27 / 1.24 | 1.01 / 1.13 | 1.30 / 1.22 | 1.33 / 1.18 |
| ECDSA P-521 sign / verify | 0.03 / 0.04 | 0.04 / 0.05 | 0.57 / 0.31 | 1.77 / 1.05 | 2.04 / 1.28 | 1.91 / 1.22 | 1.89 / 1.14 |
| RSA-2048 PSS verify | 0.23 | 0.25 | 0.71 | 0.83 | 0.94 | 0.94 | 1.05 |
| Ed25519 sign / verify | 0.60 / 0.65 | 0.55 / 0.57 | 1.06 / 1.43 | 1.18 / 1.57 | 0.79 / 1.28 | 1.31 / 1.66 | 1.22 / 1.74 |
| X25519 keygen | 0.33 | 0.54 | 1.21 | 1.29 | 0.82 | 1.29 | 1.16 |
