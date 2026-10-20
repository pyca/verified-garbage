# rustls benchmarks: verified-garbage vs aws-lc-rs

## Refresh at e12ee485

Measured on main e12ee485 (after this round's ML-KEM decapsulation, x86
Keccak ×4, AES-GCM and AArch64 changes), with this branch's provider at
e3f347caf, the same rustls (91aebe5d) and aws-lc-rs (1.18.1), on the same
class of host as below: a 2.1 GHz Intel Xeon with AVX-512 IFMA, VAES and
VPCLMULQDQ, pinned to one core. `bench/run.sh 3`, so each value is the
median of three rounds; the host was noisier than for the run below.

Geometric means of verified-garbage / aws-lc-rs − 1 (positive: faster):

| Group | Scenarios | Speed |
|---|---:|---:|
| Full handshakes, client RSA-2048 | 12 | +38% |
| Full handshakes, server RSA-2048 | 12 | +19% |
| Full handshakes, client / server P-256 | 8 / 8 | +47% / +49% |
| Full handshakes, client / server P-384 | 2 / 2 | +36% / +53% |
| Full handshakes, client / server Ed25519 | 6 / 6 | +57% / +50% |
| Resumed handshakes | 112 | +32% |
| Bulk ChaCha20-Poly1305 | 12 | +49% |
| Bulk AES-128-GCM | 8 | +8% |
| Bulk AES-256-GCM | 12 | +7% |
| All | 200 | +32% |

verified-garbage is faster in 194 of the 200 scenarios. Of the six that are
not, the three resumed TLS 1.2 RSA ChaCha20-Poly1305 scenarios (0.89–0.95)
do no RSA and were +4% to +6% in the run below, so they read as noise.
The other three are TLS 1.2 AES-GCM bulk at `max_fragment_size` 10000
(0.97–1.00).

Weak spots this run shows, each handed to a session:

* AES-GCM sealing a TLS 1.3 record out of place (16384 + 1 bytes, two
  pieces into a separate buffer): 0.98× (AES-128) and 0.96× (AES-256)
  against aws-lc-rs sealing in place, while in place is 1.07–1.08×. Its
  time moves by up to ~15% with the output buffer's offset from the
  payload, so it may be aliasing between the input and output streams.
* Ed25519 sign through the provider: 0.98×.
* secp256r1 key generation (`client start`): 1.01×, while ECDSA P-256
  sign, which also multiplies the base point, is 1.50×.
* ChaCha20-Poly1305 records of 16–256 bytes: 0.99–1.03×.
* RSA signing: 1.16× at 2048, 1.09× at 3072, 1.04× at 4096 (PSS through
  the provider).

## Every rustls-bench test at d713a393

Measured on main d713a393 (which includes the AVX-512 IFMA RSA public-key
operation, #2705), with this branch's provider at 0032f886a, rustls 91aebe5d
(with `bench/rustls.patch`) and aws-lc-rs 1.18.1 (aws-lc-sys 0.45.0).

* **Hardware:** a 2.1 GHz Intel Xeon, 4 vCPUs (one thread per core) in a
  KVM guest, with AVX-512 (IFMA, VAES, VPCLMULQDQ), SHA-NI and ADX; every
  run pinned to one core (`taskset -c 2`), with `VG_CPU_FEATURES` unset.
* **Command:** `rustls-bench --provider <p> --api buffered`: all 224 tests,
  multiplier 1. Three rounds per provider, alternating which provider ran
  first, and each value is the median of its three rounds.
* **Units:** handshakes per second; bulk throughput in MiB/s (rustls-bench
  prints "MB/s" but divides by 1024×1024). The percentage is
  verified-garbage / aws-lc-rs − 1, so a positive number means that
  verified-garbage is faster.

Geometric means of the percentages:

| Group | Tests | TLS 1.2 | TLS 1.3 | All |
|---|---:|---:|---:|---:|
| Full handshakes, client (RSA-2048 / P-256 / Ed25519) | 28 | +27% / +28% / +30% | +28% / +29% / +36% | +29% |
| Full handshakes, server (RSA-2048 / P-256 / Ed25519) | 28 | +6% / +29% / +31% | +10% / +29% / +29% | +20% |
| Resumed handshakes (session IDs and tickets) | 112 | +18% to +27% | +28% to +34% | +26% |
| Bulk, ChaCha20-Poly1305 | 12 | +43% | +43% | |
| Bulk, AES-128-GCM | 16 | +8% | +18% | |
| Bulk, AES-256-GCM | 28 | +3% | +9% | |
| Bulk, all | 56 | | | +16% |

verified-garbage is faster in 214 of the 224 tests. The 10 tests where
verified-garbage is slower are all within noise. They are TLS 1.2
AES-256-GCM bulk with ECDSA and Ed25519, TLS 1.3 AES-128-GCM bulk with
Ed25519 at mfs=10000, and two resumed TLS 1.2 ChaCha20-Poly1305 RSA tests.
The full handshakes that RSA signing dominates, on the server side, are
close to ties (+1% to +11%). The client side of RSA-2048 full handshakes
verifies with the IFMA public-key operation, and is +34% to +58%.

Noise: each test runs for well under a second at multiplier 1 on a shared
VM, and single rounds dip by 20–40%. The spread of a test's three rounds,
(max − min) / median, is 11% at the median and ~35% (handshakes) or ~25%
(bulk) at the 90th percentile. † marks tests where the ranges of the two
providers' rounds overlap: treat those as ties. In 150 tests,
verified-garbage's slowest round beats aws-lc-rs's fastest. In no test is
verified-garbage's fastest round slower than aws-lc-rs's slowest.

<details><summary>All 224 tests</summary>

| Scenario | verified-garbage | aws-lc-rs | % faster or slower |
|---|---:|---:|---:|
| **Handshakes (handshakes/s)** | | | |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 no-resume server-auth client | 10,583 | 7,439 | +42% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 no-resume server-auth server † | 2,496 | 2,451 | +2% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 no-resume mutual client | 2,180 | 1,999 | +9% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 no-resume mutual server | 2,270 | 2,127 | +7% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 sessionid server-auth client † | 129,787 | 127,628 | +2% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 sessionid server-auth server † | 144,482 | 145,959 | −1% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 sessionid mutual client | 130,316 | 122,487 | +6% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 sessionid mutual server | 141,354 | 135,620 | +4% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 tickets server-auth client † | 123,504 | 109,249 | +13% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 tickets server-auth server † | 125,516 | 107,192 | +17% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 tickets mutual client † | 73,061 | 76,998 | −5% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 tickets mutual server | 67,252 | 49,297 | +36% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 no-resume server-auth client † | 5,071 | 3,898 | +30% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 no-resume server-auth server † | 17,851 | 14,298 | +25% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 no-resume mutual client | 4,553 | 3,508 | +30% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 no-resume mutual server | 6,007 | 4,650 | +29% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 sessionid server-auth client | 138,754 | 113,439 | +22% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 sessionid server-auth server | 153,448 | 119,375 | +29% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 sessionid mutual client | 133,139 | 119,282 | +12% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 sessionid mutual server | 143,554 | 122,644 | +17% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 tickets server-auth client | 126,989 | 90,243 | +41% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 tickets server-auth server | 127,911 | 86,349 | +48% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 tickets mutual client | 95,841 | 80,480 | +19% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 tickets mutual server | 91,120 | 59,465 | +53% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 no-resume server-auth client | 10,809 | 6,845 | +58% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 no-resume server-auth server † | 2,512 | 2,257 | +11% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 no-resume mutual client | 2,213 | 1,969 | +12% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 no-resume mutual server | 2,335 | 2,109 | +11% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 sessionid server-auth client † | 138,746 | 128,577 | +8% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 sessionid server-auth server † | 160,104 | 147,707 | +8% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 sessionid mutual client † | 138,557 | 125,625 | +10% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 sessionid mutual server | 150,956 | 141,391 | +7% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 tickets server-auth client | 131,529 | 114,097 | +15% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 tickets server-auth server | 135,402 | 109,042 | +24% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 tickets mutual client | 83,612 | 75,319 | +11% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 tickets mutual server | 77,337 | 48,725 | +59% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 no-resume server-auth client | 9,759 | 7,076 | +38% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 no-resume server-auth server † | 2,452 | 2,429 | +1% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 no-resume mutual client † | 2,005 | 1,854 | +8% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 no-resume mutual server † | 2,099 | 1,965 | +7% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 sessionid server-auth client | 84,797 | 72,692 | +17% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 sessionid server-auth server | 91,464 | 78,355 | +17% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 sessionid mutual client | 85,319 | 66,374 | +29% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 sessionid mutual server | 90,624 | 69,784 | +30% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 tickets server-auth client † | 77,205 | 52,082 | +48% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 tickets server-auth server | 78,117 | 50,882 | +54% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 tickets mutual client | 46,268 | 32,109 | +44% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 tickets mutual server | 43,418 | 24,949 | +74% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 no-resume server-auth client | 4,645 | 3,722 | +25% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 no-resume server-auth server | 15,276 | 11,633 | +31% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 no-resume mutual client | 4,248 | 3,336 | +27% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 no-resume mutual server | 5,590 | 4,298 | +30% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 sessionid server-auth client † | 74,850 | 73,309 | +2% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 sessionid server-auth server † | 80,547 | 78,315 | +3% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 sessionid mutual client | 89,164 | 67,716 | +32% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 sessionid mutual server | 92,299 | 72,120 | +28% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 tickets server-auth client | 81,136 | 64,509 | +26% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 tickets server-auth server | 82,091 | 60,097 | +37% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 tickets mutual client † | 56,064 | 45,122 | +24% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 tickets mutual server | 54,565 | 36,489 | +50% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 no-resume server-auth client † | 1,549 | 1,304 | +19% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 no-resume server-auth server | 9,414 | 6,416 | +47% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 no-resume mutual client | 1,457 | 1,118 | +30% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 no-resume mutual server | 2,034 | 1,565 | +30% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 sessionid server-auth client † | 80,180 | 76,190 | +5% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 sessionid server-auth server † | 86,277 | 81,388 | +6% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 sessionid mutual client † | 81,081 | 77,134 | +5% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 sessionid mutual server † | 85,936 | 81,131 | +6% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 tickets server-auth client | 81,368 | 70,255 | +16% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 tickets server-auth server | 82,038 | 68,194 | +20% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 tickets mutual client † | 55,783 | 50,134 | +11% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 tickets mutual server | 52,293 | 40,750 | +28% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 no-resume server-auth client † | 7,912 | 5,749 | +38% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 no-resume server-auth server † | 19,000 | 15,652 | +21% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 no-resume mutual client | 5,981 | 4,419 | +35% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 no-resume mutual server † | 7,417 | 5,890 | +26% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 sessionid server-auth client † | 77,010 | 72,225 | +7% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 sessionid server-auth server † | 82,733 | 77,607 | +7% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 sessionid mutual client | 88,307 | 69,182 | +28% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 sessionid mutual server | 93,412 | 71,766 | +30% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 tickets server-auth client | 81,785 | 61,485 | +33% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 tickets server-auth server | 82,643 | 61,653 | +34% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 tickets mutual client | 55,712 | 46,883 | +19% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 tickets mutual server | 53,728 | 39,558 | +36% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 no-resume server-auth client | 7,174 | 5,365 | +34% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 no-resume server-auth server † | 2,309 | 2,275 | +1% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 no-resume mutual client | 2,015 | 1,723 | +17% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 no-resume mutual server † | 2,155 | 1,893 | +14% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 sessionid server-auth client | 12,616 | 9,535 | +32% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 sessionid server-auth server | 14,715 | 11,154 | +32% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 sessionid mutual client | 13,199 | 9,576 | +38% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 sessionid mutual server | 14,920 | 10,793 | +38% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 tickets server-auth client | 12,808 | 10,092 | +27% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 tickets server-auth server | 14,958 | 11,507 | +30% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 tickets mutual client | 11,187 | 9,844 | +14% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 tickets mutual server | 11,760 | 9,431 | +25% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 no-resume server-auth client | 6,775 | 4,725 | +43% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 no-resume server-auth server | 2,317 | 2,137 | +8% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 no-resume mutual client | 2,043 | 1,675 | +22% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 no-resume mutual server | 2,144 | 1,810 | +18% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 sessionid server-auth client | 10,199 | 7,739 | +32% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 sessionid server-auth server | 10,986 | 8,479 | +30% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 sessionid mutual client | 9,884 | 7,418 | +33% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 sessionid mutual server | 10,517 | 7,940 | +32% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 tickets server-auth client | 9,379 | 7,773 | +21% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 tickets server-auth server | 10,174 | 8,305 | +22% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 tickets mutual client | 7,796 | 6,709 | +16% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 tickets mutual server | 7,613 | 6,205 | +23% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 no-resume server-auth client | 3,907 | 2,650 | +47% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 no-resume server-auth server | 9,731 | 6,373 | +53% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 no-resume mutual client | 3,412 | 2,665 | +28% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 no-resume mutual server | 4,288 | 3,432 | +25% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 sessionid server-auth client | 9,841 | 6,367 | +55% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 sessionid server-auth server | 10,586 | 6,935 | +53% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 sessionid mutual client | 9,402 | 7,135 | +32% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 sessionid mutual server | 10,058 | 7,709 | +30% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 tickets server-auth client † | 9,571 | 7,601 | +26% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 tickets server-auth server † | 10,322 | 8,109 | +27% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 tickets mutual client | 9,029 | 7,129 | +27% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 tickets mutual server | 9,071 | 7,026 | +29% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 no-resume server-auth client | 5,392 | 4,011 | +34% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 no-resume server-auth server † | 10,121 | 8,206 | +23% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 no-resume mutual client | 5,214 | 3,677 | +42% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 no-resume mutual server | 6,385 | 4,562 | +40% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 sessionid server-auth client | 10,289 | 7,524 | +37% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 sessionid server-auth server | 11,043 | 8,176 | +35% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 sessionid mutual client | 9,913 | 7,470 | +33% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 sessionid mutual server | 10,577 | 8,019 | +32% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 tickets server-auth client | 10,056 | 7,247 | +39% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 tickets server-auth server | 10,872 | 7,648 | +42% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 tickets mutual client | 9,603 | 6,843 | +40% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 tickets mutual server | 9,824 | 6,808 | +44% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 no-resume server-auth client | 7,359 | 5,309 | +39% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 no-resume server-auth server † | 2,336 | 2,248 | +4% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 no-resume mutual client † | 2,096 | 1,796 | +17% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 no-resume mutual server † | 2,229 | 1,951 | +14% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 sessionid server-auth client | 12,818 | 9,504 | +35% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 sessionid server-auth server | 14,852 | 11,143 | +33% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 sessionid mutual client | 12,586 | 9,071 | +39% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 sessionid mutual server | 14,136 | 10,436 | +35% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 tickets server-auth client | 13,201 | 10,141 | +30% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 tickets server-auth server | 15,275 | 11,690 | +31% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 tickets mutual client | 12,287 | 9,695 | +27% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 tickets mutual server | 13,028 | 9,383 | +39% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 no-resume server-auth client | 4,297 | 3,062 | +40% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 no-resume server-auth server | 12,385 | 8,887 | +39% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 no-resume mutual client | 3,261 | 3,110 | +5% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 no-resume mutual server † | 4,311 | 4,130 | +4% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 sessionid server-auth client | 11,988 | 10,410 | +15% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 sessionid server-auth server | 13,520 | 12,122 | +12% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 sessionid mutual client | 12,166 | 10,161 | +20% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 sessionid mutual server | 13,839 | 11,690 | +18% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 tickets server-auth client | 12,240 | 9,498 | +29% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 tickets server-auth server | 14,225 | 10,842 | +31% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 tickets mutual client † | 11,745 | 9,769 | +20% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 tickets mutual server † | 12,704 | 10,168 | +25% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 no-resume server-auth client | 5,828 | 4,570 | +28% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 no-resume server-auth server | 12,671 | 10,998 | +15% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 no-resume mutual client | 5,808 | 4,116 | +41% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 no-resume mutual server | 7,585 | 5,400 | +40% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 sessionid server-auth client | 12,862 | 9,368 | +37% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 sessionid server-auth server | 14,847 | 10,972 | +35% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 sessionid mutual client | 12,922 | 9,542 | +35% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 sessionid mutual server | 14,690 | 10,962 | +34% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 tickets server-auth client † | 12,689 | 10,202 | +24% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 tickets server-auth server † | 14,856 | 11,530 | +29% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 tickets mutual client | 11,842 | 9,467 | +25% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 tickets mutual server | 12,866 | 10,018 | +28% |
| **Bulk (MiB/s; rustls-bench labels it MB/s)** | | | |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 bulk mfs=default send | 2,368 | 1,642 | +44% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 bulk mfs=default recv | 2,300 | 1,639 | +40% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 bulk mfs=10000 send | 2,264 | 1,656 | +37% |
| TLS1.2 TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 RSA-2048 bulk mfs=10000 recv | 2,236 | 1,625 | +38% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 bulk mfs=default send | 2,466 | 1,698 | +45% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 bulk mfs=default recv | 2,417 | 1,669 | +45% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 bulk mfs=10000 send | 2,397 | 1,624 | +48% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 ECDSA P-256 bulk mfs=10000 recv | 2,389 | 1,589 | +50% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 bulk mfs=default send † | 10,182 | 9,579 | +6% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 bulk mfs=default recv | 9,757 | 8,724 | +12% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 bulk mfs=10000 send † | 9,764 | 9,359 | +4% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 RSA-2048 bulk mfs=10000 recv † | 8,972 | 8,306 | +8% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 bulk mfs=default send † | 9,005 | 8,684 | +4% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 bulk mfs=default recv † | 8,422 | 7,867 | +7% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 bulk mfs=10000 send † | 8,463 | 8,254 | +3% |
| TLS1.2 TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 RSA-2048 bulk mfs=10000 recv † | 7,868 | 7,463 | +5% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 bulk mfs=default send † | 7,917 | 8,715 | −9% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 bulk mfs=default recv † | 7,507 | 8,081 | −7% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 bulk mfs=10000 send † | 7,621 | 7,649 | 0% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-256 bulk mfs=10000 recv † | 7,020 | 6,692 | +5% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 bulk mfs=default send | 9,233 | 8,966 | +3% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 bulk mfs=default recv † | 8,535 | 7,683 | +11% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 bulk mfs=10000 send † | 8,708 | 8,309 | +5% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 ECDSA P-384 bulk mfs=10000 recv † | 8,482 | 7,052 | +20% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 bulk mfs=default send † | 8,782 | 9,001 | −2% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 bulk mfs=default recv † | 8,358 | 8,431 | −1% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 bulk mfs=10000 send † | 8,640 | 8,438 | +2% |
| TLS1.2 TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 Ed25519 bulk mfs=10000 recv † | 7,940 | 7,552 | +5% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 bulk mfs=default send | 2,454 | 1,698 | +45% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 bulk mfs=default recv | 2,404 | 1,725 | +39% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 bulk mfs=10000 send | 2,286 | 1,571 | +46% |
| TLS1.3 TLS13_CHACHA20_POLY1305_SHA256 RSA-2048 bulk mfs=10000 recv | 2,233 | 1,575 | +42% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 bulk mfs=default send † | 9,369 | 8,704 | +8% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 bulk mfs=default recv † | 8,995 | 8,295 | +8% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 bulk mfs=10000 send | 8,951 | 8,420 | +6% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 RSA-2048 bulk mfs=10000 recv | 8,058 | 7,555 | +7% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 bulk mfs=default send † | 8,959 | 8,971 | 0% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 bulk mfs=default recv † | 8,575 | 8,423 | +2% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 bulk mfs=10000 send | 9,124 | 7,542 | +21% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 ECDSA P-256 bulk mfs=10000 recv | 8,041 | 6,750 | +19% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 bulk mfs=default send † | 9,680 | 8,826 | +10% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 bulk mfs=default recv † | 9,331 | 8,326 | +12% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 bulk mfs=10000 send † | 9,095 | 8,324 | +9% |
| TLS1.3 TLS13_AES_256_GCM_SHA384 Ed25519 bulk mfs=10000 recv † | 8,272 | 7,438 | +11% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 bulk mfs=default send | 10,733 | 8,040 | +33% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 bulk mfs=default recv | 10,368 | 7,279 | +42% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 bulk mfs=10000 send | 10,094 | 7,275 | +39% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 RSA-2048 bulk mfs=10000 recv | 8,845 | 6,371 | +39% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 bulk mfs=default send | 10,474 | 8,863 | +18% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 bulk mfs=default recv † | 10,040 | 8,970 | +12% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 bulk mfs=10000 send | 9,870 | 7,989 | +24% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 ECDSA P-256 bulk mfs=10000 recv | 8,777 | 7,063 | +24% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 bulk mfs=default send † | 10,462 | 10,017 | +4% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 bulk mfs=default recv † | 10,006 | 9,469 | +6% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 bulk mfs=10000 send † | 9,057 | 9,532 | −5% |
| TLS1.3 TLS13_AES_128_GCM_SHA256 Ed25519 bulk mfs=10000 recv † | 7,909 | 8,387 | −6% |

</details>

## Earlier runs

The run at 7c42c0e1, in detail (a native Cascade Lake run at f4f61d14 and a refresh at ecd4fc1e come first): measured with `bench/run.sh 5`
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

## Native Cascade Lake at f4f61d14 (noisy host)

Measured with `bench/run.sh 5` on main f4f61d14 (with #1776, #1790, #1792,
#1845, #1924 and the other merges since ecd4fc1e), on a 2.8 GHz Intel Xeon
**Cascade Lake**: AVX-512F/BW/VL/VNNI, ADX, AES-NI and PCLMULQDQ, but no
IFMA, VAES, VPCLMULQDQ or SHA-NI. So this is the class the masked runs below
emulated, natively, with no `VG_CPU_FEATURES` or `OPENSSL_ia32cap`. The host
was noisy (single rows move by ±5–10% between rounds); read the geometric
means and ranges rather than single rows.

| rustls-bench | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 1.03–1.20 | 0.98–1.18 | 1.07–1.21 | 1.03–1.22 | 1.11–1.27 | 1.02–1.49 |
| ECDSA P-384 (TLS 1.2 only) | 1.24 | 1.37 | 1.27 | 1.22 | | 1.19–1.79 |
| RSA-2048 | 0.98–1.03 | 0.86–0.90 | 0.89–0.95 | 0.86–0.97 | 1.06–1.24 | 1.02–1.56 |
| Ed25519 | 1.14–1.32 | 1.13 | 1.11–1.24 | 1.10–1.21 | 1.14–1.26 | 1.09–1.51 |

| Bulk, send / receive | 16 KiB records | 10000 B records |
|---|---:|---:|
| TLS 1.3 AES-128-GCM | 0.85 / 0.90 | 0.94 / 0.99 |
| TLS 1.3 AES-256-GCM | 0.88 / 0.92 | 0.93 / 0.97 |
| TLS 1.3 ChaCha20-Poly1305 | 1.13 / 1.11 | 1.17 / 1.24 |
| TLS 1.2 AES-GCM | 0.89–0.96 / 0.95–1.02 | 0.84–1.01 / 0.90–1.03 |
| TLS 1.2 ChaCha20-Poly1305 | 1.11–1.14 / 1.09–1.12 | 1.04–1.11 / 1.12–1.16 |

What remains below parity on this class:

* **AES-128-GCM sealing at 4–16 KiB: 0.83–0.93** (aws-lc-compare in place
  16384 B 0.83, out of place 16384+1 B 0.92, 4096+1 B 0.93), so bulk sending
  at 0.84–0.95. AES-256 in place is 1.02 at 16384 B, so AES-128's loop or its
  dispatch is the suspect. Everything at or under 1 KiB is 1.03–1.8.
* **RSA-2048 signing: 0.78–0.85** (3072 and 4096 are 0.95–1.03), so RSA-2048
  server handshakes at 0.86–0.97. Lazy Montgomery reduction (a Spec change,
  approved) is the main lever.
* **ChaCha20-Poly1305 below 1 KiB: 0.66–0.86** (in place 0 B 259 vs 186 ns,
  opening 1 KiB 0.80) on the AVX-512 path without IFMA, a fixed cost; bulk
  is 1.11–1.29.
* **Key exchange: no real gap.** Provider-level kx rows are noise on this
  host (three reruns put secp256r1's server start_and_complete at 1.11,
  1.04 and 1.76, X25519's at 0.69–1.37). The steadier aws-lc-compare rows,
  three rounds each: P-256 fixed-base keygen 0.98–1.03, P-256 ECDH 1.28,
  X25519 keygen 1.10 and X25519 Diffie-Hellman about even (28.3–28.8 µs
  against about 26–31 µs).
* **HKDF-SHA-384 extract + expand: 0.91–0.94** (no SHA-NI; HMAC-SHA-384 alone is 1.23).

## Refresh at ecd4fc1e (noisy host)

The same machine, after main gained AES-GCM's AES-NI + AVX loop for every
block from the 16th and its call-free seal (#1684, #1688), SHA-256's
shorter AVX2 rounds and wider copies (#1671, #1683, #1686), RSA squaring
changes (#1695, #1696; #1685 was reverted by #1693 for slowing Zen 4 and 5)
and an X25519 ladder change (#1682). **The host was noisy:** a primitive's
time moved by up to 1.5x between rounds (RSA-2048 verification 21–34 µs), so
single primitive rows are rough. The handshake and bulk geometric means,
over many scenarios, are steadier.

| rustls-bench, full CPU | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 1.24–1.30 | 1.22–1.27 | 1.30–1.38 | 1.30–1.38 | 1.20–1.32 | 1.14–1.38 |
| ECDSA P-384 (TLS 1.2 only) | 1.21 | 1.50 | 1.23 | 1.25 | | 1.16–1.39 |
| RSA-2048 | 1.12–1.22 | 1.03–1.13 | 1.03–1.12 | 1.02–1.11 | 1.13–1.27 | 1.08–1.55 |
| Ed25519 | 1.31–1.44 | 1.18–1.24 | 1.33 | 1.34 | 1.16–1.31 | 1.19–1.50 |

| rustls-bench, Cascade Lake class (emulated) | client, full | server, full | client, mutual | server, mutual | resumed (TLS 1.3) | resumed (TLS 1.2) |
|---|---:|---:|---:|---:|---:|---:|
| ECDSA P-256 | 1.28–1.34 | 1.10–1.29 | 1.22–1.30 | 1.25–1.29 | 1.10–1.28 | 1.11–1.57 |
| ECDSA P-384 (TLS 1.2 only) | 1.26 | 1.46 | 1.36 | 1.36 | | 1.01–1.49 |
| RSA-2048 | 1.04–1.12 | 0.90–0.93 | 0.96–0.97 | 0.96 | 1.12–1.32 | 1.13–1.75 |
| Ed25519 | 1.17–1.22 | 1.11–1.20 | 1.11–1.21 | 1.14–1.17 | 1.15–1.34 | 1.15–1.61 |

| Bulk, send / receive | full CPU, 16 KiB | full CPU, 10000 B | Cascade Lake, 16 KiB | Cascade Lake, 10000 B |
|---|---:|---:|---:|---:|
| TLS 1.3 AES-GCM | 1.03–1.05 / 0.99–1.03 | 1.02–1.04 / 0.93–1.02 | 0.95–0.98 / 1.03–1.07 | 0.80–0.89 / 0.89–1.01 |
| TLS 1.3 ChaCha20-Poly1305 | 1.41 / 1.49 | 1.33 / 1.34 | 1.31 / 1.34 | 1.21 / 1.26 |
| TLS 1.2 AES-GCM | 1.01–1.03 / 0.97–1.01 | 0.97–1.01 / 0.95–1.00 | 0.90–0.94 / 0.99–1.03 | 0.90–0.93 / 1.01–1.06 |
| TLS 1.2 ChaCha20-Poly1305 | 1.28–1.32 / 1.28–1.31 | 1.30–1.31 / 1.37 | 1.27–1.37 / 1.25–1.38 | 1.24 / 1.30 |

Every handshake on the full CPU is now faster than aws-lc-rs's (1.02–1.55),
and ChaCha20-Poly1305 bulk is 1.28–1.49. What remains below parity:

* **Cascade Lake class, AES-GCM sending: 0.80–0.98** (10000-byte records
  worst), and out-of-place sealing at 4096+1 B (0.75–0.94 across rounds).
* **Cascade Lake class, RSA private-key operations: 0.83–0.95** (signing at
  every size), hence RSA-2048 server handshakes at 0.90–0.93.
* **Within noise or single rounds:** P-384 ECDH (0.85–1.02), X25519 Diffie-Hellman
  on the Cascade Lake class (0.93), AES-GCM receive with 10000-byte records
  (0.89–1.02).

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

The code paths of a CPU without IFMA, VAES or SHA-NI are measured in the
next section.

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

| | 8532494 (first run) | 36ff93f9 | 7cdac586 | 93f54441 | b5b67857 (noisy) | a70d41fa | 7c42c0e1 | ecd4fc1e (noisy) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| P-256 full handshake, client / server | 0.11–0.15 / 0.16–0.24 | 0.52–0.60 / 0.74–0.91 | 0.71–0.77 / 0.99–1.00 | 1.25–1.27 / 1.20–1.23 | 0.90–1.27 / 0.80–1.22 | 1.23–1.28 / 1.15–1.26 | 1.10–1.37 / 1.04–1.29 | 1.24–1.30 / 1.22–1.27 |
| RSA-2048 full handshake, client / server | 0.42–0.47 / 0.93 | 0.48–0.55 / 0.58–0.59 | 0.91–0.96 / 1.02–1.05 | 1.06 / 1.08 | 0.84–1.03 / 0.71–0.86 | 1.07–1.11 / 1.05–1.07 | 1.19–1.22 / 1.12–1.15 | 1.12–1.22 / 1.03–1.13 |
| Ed25519 full handshake, client / server | 0.73–0.74 / 0.78–0.83 | 0.64–0.73 / 0.76–0.91 | 1.14–1.22 / 1.01–1.04 | 1.26–1.29 / 1.08–1.13 | 1.18–1.21 / 1.02–1.10 | 1.28–1.62 / 1.16–1.38 | 1.18–1.34 / 1.00–1.22 | 1.31–1.44 / 1.18–1.24 |
| Bulk AES-GCM / ChaCha20-Poly1305 (16 KiB) | 0.76–0.83 / 0.98–1.01 | 0.88–0.93 / 1.37–1.39 | 0.85–0.95 / 1.30–1.31 | 0.89–0.94 / 1.24–1.27 | 0.72–1.01 / 1.08–1.09 | 0.96–1.02 / 1.32–1.36 | 1.02–1.05 / 1.09–1.18 | 1.03–1.05 / 1.41–1.49 |
| AES-128/256-GCM 16 KiB record seal | 0.72 / 0.78 | 0.88 / 0.86 | 0.85 / 0.86 | 0.97 / 1.02 | 0.79 / 0.80 | 1.03 / 1.06 | 1.12 / 1.11 | 1.06 / 1.07 |
| ECDSA P-256 sign / verify | 0.05 / 0.08 | 0.56 / 0.44 | 1.03 / 0.67 | 1.27 / 1.24 | 1.01 / 1.13 | 1.30 / 1.22 | 1.33 / 1.18 | 1.41 / 1.30 |
| ECDSA P-521 sign / verify | 0.03 / 0.04 | 0.04 / 0.05 | 0.57 / 0.31 | 1.77 / 1.05 | 2.04 / 1.28 | 1.91 / 1.22 | 1.89 / 1.14 | 2.19 / 1.11 |
| RSA-2048 PSS verify | 0.23 | 0.25 | 0.71 | 0.83 | 0.94 | 0.94 | 1.05 | 1.06 |
| Ed25519 sign / verify | 0.60 / 0.65 | 0.55 / 0.57 | 1.06 / 1.43 | 1.18 / 1.57 | 0.79 / 1.28 | 1.31 / 1.66 | 1.22 / 1.74 | 1.31 / 1.58 |
| X25519 keygen | 0.33 | 0.54 | 1.21 | 1.29 | 0.82 | 1.29 | 1.16 | 1.54 |
