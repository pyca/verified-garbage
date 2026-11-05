# Comparing AES-GCM-SIV

The `aes_gcm_siv` benchmark measures 128- and 256-bit keys at 64 B,
1 KiB, 16 KiB and 1 MiB. Each operation includes key setup; decryption
also includes restoring the ciphertext. All libraries operate in place
and use a separate 16-byte tag, a 12-byte nonce and 16 bytes of AAD.
OpenSSL's cipher fetch is outside timing, like AWS-LC's algorithm lookup.
Context creation, key expansion and context destruction are timed.

Build OpenSSL 4.x with assembly enabled, then point rust-openssl at it:

```sh
./Configure --prefix=/absolute/path/openssl4 --libdir=lib no-shared no-tests
make -j4
make install_sw
export OPENSSL_DIR=/absolute/path/openssl4 OPENSSL_STATIC=1
"$OPENSSL_DIR/bin/openssl" version -a
cargo bench --manifest-path bench/Cargo.toml --features openssl-gcm-siv --no-run
```

`openssl-gcm-siv` requires OpenSSL 3.2 or later; it fails if cipher fetching
fails, rather than silently omitting the comparison. It is opt-in so that
OpenSSL 3.0 runners can still benchmark VG and AWS-LC.

On x86-64, check hardware first:

```sh
grep -o 'avx512ifma\|vaes\|vpclmulqdq\|sha_ni' /proc/cpuinfo | sort -u
```

`gcm_siv_features.py` prints a pair of feature ceilings and optionally runs
a command with them. Its profiles cover every VG AES-GCM-SIV backend,
including backends with hardware AES but software hashing and vice versa.
`scalar_avx2`, `aesni_avx2`, and `pclmul_avx2` exercise AVX2 copies
independently of VAES/VPCLMULQDQ. `aesni_pclmul_avx` also allows AVX2:
on updated VG it selects the AVX2-copy AES-NI/PCLMUL implementation.
When both AAD and text are shorter than 128 bytes, VG uses the ordinary
instance: neither copy loop would use AVX2 at those lengths.
For example:

```sh
python3 bench/gcm_siv_features.py aesni_pclmul_avx
VG_BENCHES=aes_gcm_siv python3 bench/gcm_siv_features.py aesni_pclmul_avx -- \
  cargo bench --manifest-path bench/Cargo.toml --features openssl-gcm-siv -- \
  --sample-size 30 --warm-up-time 0.2 --measurement-time 0.5
python3 bench/gcm_siv_features.py vaes_vpclmul -- \
  cargo test --manifest-path bench/Cargo.toml --features openssl-gcm-siv \
  --test aes_gcm_siv --release
```

Use `--help` for profile names. `VG_CPU_FEATURES` is an allowlist intersected
with detected hardware features; the benchmark dependency enables
`cpu-features-env`. `OPENSSL_ia32cap` uses removal masks for the first two
64-bit logical vectors, and zeros the three newer OpenSSL 4.x vectors.
The masks clear AES-NI, PCLMULQDQ, SSSE3, AVX, AVX2, VAES and VPCLMULQDQ
unless allowed, and clear unselected AVX-512 and other crypto capabilities.
They preserve baseline SSE2 and CPU vendor/cache-topology flags.
See OpenSSL's `OPENSSL_ia32cap(3)` for bit positions. AWS-LC reads the same
first two masks. Its GCM-SIV assembly dispatch checks only AES-NI and AVX,
not PCLMULQDQ: in the `vaes` profile (AVX enabled, PCLMUL disabled), AWS-LC
still uses PCLMUL instructions. Treat its numbers in that profile as a
reference only, not a feature-equivalent comparison. VG and OpenSSL honor
the selected ceilings. These ceilings are not a guarantee
that each library dispatches to the same implementation. Masking features
on a modern CPU does not reproduce the instruction costs of an older CPU.

Run each profile in a fresh process: both libraries cache feature detection.
Use the same masks for baseline and candidate and interleave repeated runs
of preserved binaries. Criterion's automatic comparison with its previous
run is meaningless when that run used another profile; compare matching
profiles' absolute times instead.

The differential test checks both key sizes, empty messages/AAD, unaligned
buffers, tails and batch boundaries, and checks that VG clears plaintext
after a bad tag. Published known-answer vectors remain in VG's own tests.
