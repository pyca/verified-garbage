# rustls benchmarks: verified-garbage vs aws-lc-rs

Measured 2026-10-06 with `bench/run.sh 5`, verified-garbage at 36ff93f9,
rustls 91aebe5d, aws-lc-rs 1.18.1. One core (`taskset -c 2`) of a 2.8 GHz
Intel Xeon (Cascade Lake class: AVX-512F/BW/VL, ADX, AES-NI, PCLMULQDQ;
**no** SHA-NI, AVX512-IFMA, VAES or VPCLMULQDQ). Throughput is noisy on this
VM (±10%), so read the ratios, and treat differences under ~10% as noise.

The first run (2026-10-05, verified-garbage 8532494) was on a CPU that has
SHA-NI, AVX512-IFMA, VAES and VPCLMULQDQ. Both libraries pick different code
on that CPU (IFMA RSA, VAES AES-GCM), so ratios move between the two runs for
hardware reasons as well as library changes. That run's ratios are in
"Changes since the first run" below.

## rustls-bench (`--api buffered`, median of 5 runs)

Every ratio in this file is verified-garbage's speed relative to
aws-lc-rs's: below 1 is slower (0.5 is half as fast). For throughput it is
verified-garbage / aws-lc-rs; for times, aws-lc-rs / verified-garbage. Each
rustls-bench ratio is the geometric mean over the row's cipher suites; a range spans TLS 1.2 and 1.3.

| | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 0.52–0.60 | 0.74–0.91 | 0.54–0.60 | 0.54–0.63 | 0.94–1.05 | 1.01–1.43 |
| RSA-2048 | 0.48–0.55 | 0.58–0.59 | 0.55–0.56 | 0.56 | 0.94–1.11 | 1.02–1.58 |
| Ed25519 | 0.64–0.73 | 0.76–0.91 | 0.65–0.70 | 0.69–0.72 | 0.96–1.08 | 1.03–1.50 |

| Bulk (TLS 1.3, send and receive) | 16 KiB records | 10000-byte records |
|---|---:|---:|
| AES-128/256-GCM | 0.88–0.93 | 0.78–0.88 |
| ChaCha20-Poly1305 | 1.37–1.39 | 1.26–1.33 |

## Primitives, through the rustls traits (`provider-primitives`)

Nanoseconds per operation, median of three runs; speed as above.

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| X25519MLKEM768 client share | 25 400 | 34 800 | 0.73 |
| X25519MLKEM768 server (encaps + DH) | 57 300 | 68 700 | 0.83 |
| X25519MLKEM768 client finish | 56 600 | 56 500 | 1.00 |
| X25519 keygen | 8 900 | 16 600 | 0.54 |
| secp256r1 keygen | 11 100 | 24 300 | 0.46 |
| secp256r1 server (keygen + DH) | 60 800 | 133 900 | 0.45 |
| secp384r1 server (keygen + DH) | 221 000 | 468 900 | 0.47 |
| ML-KEM-768 encaps / decaps | 17 200 / 23 000 | 19 400 / 23 100 | 0.89 / 1.00 |
| ECDSA P-256 sign / verify | 19 300 / 61 600 | 34 700 / 138 800 | 0.56 / 0.44 |
| ECDSA P-384 sign / verify | 102 200 / 235 900 | 133 500 / 525 200 | 0.77 / 0.45 |
| ECDSA P-521 sign / verify | 192 300 / 394 500 | 4 523 100 / 8 415 000 | 0.04 / 0.05 |
| Ed25519 sign / verify | 10 300 / 41 100 | 18 600 / 71 900 | 0.55 / 0.57 |
| RSA-2048 PSS sign / verify | 656 800 / 25 400 | 1 153 100 / 100 700 | 0.57 / 0.25 |
| RSA-3072 PSS sign / verify | 1 958 000 / 45 200 | 3 333 200 / 223 500 | 0.59 / 0.20 |
| RSA-4096 PSS sign / verify | 4 389 200 / 77 700 | 7 376 500 / 401 400 | 0.60 / 0.19 |
| RSA-2048 / 4096 load key | 193 900 / 626 900 | 1 106 500 / 7 311 000 | 0.18 / 0.09 |
| AES-128-GCM seal 16 KiB record | 2 900 | 3 280 | 0.88 |
| AES-256-GCM seal 16 KiB record | 3 400 | 3 940 | 0.86 |
| ChaCha20-Poly1305 seal 16 KiB record | 8 710 | 6 250 | 1.39 |
| HKDF-SHA256 extract + expand | 1 060 | 2 040 | 0.52 |
| transcript hash, SHA-256 / SHA-384 | 7 000 / 4 910 | 7 710 / 4 900 | 0.91 / 1.00 |
| ticket encrypt / decrypt (200 B) | 1 920 / 1 220 | 590 / 300 | 3.25 / 4.07 |

Adding up each side's operations still accounts for rustls-bench's handshake
rates. For example, a TLS 1.3 P-256 client does an X25519MLKEM768 exchange
and three ECDSA verifications: about 0.51 ms with verified-garbage against
0.27 ms with aws-lc-rs.

## Library-level (`bench/aws-lc-compare`: each library's own API)

| | aws-lc-rs | verified-garbage | speed |
|---|---:|---:|---:|
| P-256 keygen / ECDH / sign / verify | 11 300 / 60 200 / 20 000 / 60 900 | 24 000 / 109 700 / 33 400 / 133 900 | 0.47 / 0.55 / 0.60 / 0.45 |
| X25519 keygen / DH | 8 800 / 35 200 | 16 100 / 32 000 | 0.55 / 1.10 |
| RSA-2048 `PublicKey::new` (precomputes; PSS verify doesn't use it) | — | 10 500 |  |
| RSA-2048 `rsa_pss::verify` | — | 90 300 |  |
| RSA-2048 `PublicKey::public_op` (precomputed, ADX) | — | 27 300 |  |
| RSA-2048 PSS verify (whole) | 23 400 | 101 800 | 0.23 |
| AES-128-GCM seal 384 B / 1 KiB / 16 KiB | 171 / 294 / 2 780 | 248 / 317 / 3 010 | 0.69 / 0.93 / 0.92 |
| ChaCha20-Poly1305 seal 64 B / 256 B / 768 B / 1 KiB / 16 KiB | 199 / 303 / 601 / 718 / 8 410 | 338 / 416 / 684 / 651 / 5 880 | 0.59 / 0.73 / 0.88 / 1.10 / 1.43 |
| memcpy of a 16 KiB record (the provider's copy before sealing) | 176 | 176 |  |

## Where the gaps are now

Speeds relative to aws-lc-rs, as above.

1. **P-521: 0.04–0.05.** P-521 on x86-64 still uses a generic nine-word
   double-and-add ladder, with no precomputed tables, windowing or
   specialized reduction. P-256 and P-384 got all of these (#983, #1011,
   #1016, #1017, #1022, #1024).
2. **RSA-PSS verification: 0.19–0.25.** `rsa_pss::verify` still runs its
   own exponentiation from `n` and `e`, without `PublicKey`'s precomputed
   values or ADX. The library's precomputed ADX `public_op` reaches 0.75–0.86.
   #997 gave PKCS #1 verification that path, which is why RSA client
   handshakes improved (certificates are signed with PKCS #1;
   CertificateVerify uses PSS).
3. **RSA private-key operations: about 0.59 on this CPU, which lacks IFMA.**
   Loading a key is 0.09–0.18 because `PrivateKey::from_crt` checks the key
   with a full private-key operation. RSA server handshakes are 0.58 here,
   against 0.93 on the IFMA machine, where verified-garbage has an IFMA path
   for 2048-bit keys.
4. **P-256/P-384, Ed25519 and X25519 keygen: 0.44–0.76.** The x86-64 combs and
   windows raised P-256/P-384 from 0.03–0.12.
5. **AES-GCM: about 0.9**, and down to 0.69 for lengths that are not whole
   256-byte groups. Records also pay the copy into the output buffer before
   in-place sealing (#990).
6. **ChaCha20-Poly1305 below 1 KiB: 0.59–0.88**, up from 0.28–0.43. #1005 and
   #1010 handle tails in vector registers. From 1 KiB up it is 1.1–1.4.

## Changes since the first run

Speed relative to aws-lc-rs on 2026-10-05 (8532494, IFMA/VAES/SHA-NI CPU)
→ 2026-10-06 (36ff93f9, this CPU):

| | first run | now |
|---|---:|---:|
| P-256 full handshake, client / server | 0.11–0.15 / 0.16–0.24 | 0.52–0.60 / 0.74–0.91 |
| RSA-2048 full handshake, client / server | 0.42–0.47 / 0.93 | 0.48–0.55 / 0.58–0.59 |
| Ed25519 full handshake, client / server | 0.73–0.74 / 0.78–0.83 | 0.64–0.73 / 0.76–0.91 |
| Bulk AES-GCM / ChaCha20-Poly1305 (16 KiB) | 0.76–0.83 / 0.98–1.01 | 0.88–0.93 / 1.37–1.39 |
| ECDSA P-256 sign / verify | 0.05 / 0.08 | 0.56 / 0.44 |
| secp256r1 keygen / server (keygen + DH) | 0.03 / 0.09 | 0.46 / 0.45 |
| X25519 keygen | 0.32 | 0.54 |
