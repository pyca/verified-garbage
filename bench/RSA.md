# Comparing RSA construction with OpenSSL 4

Build OpenSSL with assembly enabled, and link the benchmark explicitly to it.
For example, for OpenSSL 4.1.0 (commit
`2f4e3a5fec05394068cfa7379890ab552483a8a6`):

```sh
./Configure --prefix=/absolute/path/openssl4 --libdir=lib no-shared
make -j4
make install_sw
cd /path/to/verified-garbage
OPENSSL_DIR=/absolute/path/openssl4 OPENSSL_STATIC=1 \
  cargo bench --manifest-path bench/Cargo.toml --bench primitives --no-run
/absolute/path/openssl4/bin/openssl version -a
```

`rsa_from_primes` computes the CRT values from `(n, e, d, p, q)` and loads
the key. VG also validates the CRT key and wipes its temporary private values;
the OpenSSL comparison computes the same CRT values with `BigNum` and loads
them without validating the key. OpenSSL's modular inverse is variable time;
VG's assembly is constant time with respect to the private values.

Use the same inputs for every binary, configuration and repetition. Generate
benchmark-only keys once, outside the timed runs, and keep their hashes with
the results:

```sh
mkdir -p /absolute/path/rsa-bench-keys
for bits in 2048 3072 4096; do
  /absolute/path/openssl4/bin/openssl genrsa \
    -out /absolute/path/rsa-bench-keys/$bits.pem $bits
done
sha256sum /absolute/path/rsa-bench-keys/*.pem
```

`VG_BENCH_RSA_KEYS` makes `rsa_from_primes` read `<bits>.pem` from that
directory instead of generating a new key per process. It accepts unencrypted
PEM private keys and checks the modulus size. Setup and PEM parsing are outside
the measured operation. Without the variable, the benchmark still generates
keys as before. The other RSA benchmark groups are unchanged.

## x86-64 configurations

Check the host before enabling a configuration:

```sh
grep -o 'avx512ifma\|vaes\|vpclmulqdq\|sha_ni' /proc/cpuinfo | sort -u
```

`VG_CPU_FEATURES` only restricts VG; it does not restrict OpenSSL. The following
OpenSSL masks remove the RSA-relevant extensions beyond each configuration,
while leaving unrelated capabilities alone. They only clear detected bits.
The last three capability words are cleared explicitly: OpenSSL 4 has five
64-bit capability words, described in its `OPENSSL_ia32cap(3)` manual.

| Configuration | `VG_CPU_FEATURES` | `OPENSSL_ia32cap` |
| --- | --- | --- |
| Baseline | `none` | `~0x1000000000000000:~0x5f42fc2b0128:0:0:0` |
| BMI2 + ADX | `bmi2,adx` | `~0x0:~0x5f42fc230028:0:0:0` |
| AVX-512 IFMA | `avx,bmi2,adx,avx512f,avx512ifma,avx512vl` | `~0x0:~0x5f427c020028:0:0:0` |
| Native | unset | unset |

The second word masks CPUID leaf 7, subleaf 0, EBX and ECX. The baseline
clears BMI1, AVX2, BMI2, ADX, SHA, the AVX-512 extensions, VAES, VPCLMULQDQ
and GFNI. ADX retains EBX bits 8 and 19; IFMA also retains bits 16, 21 and
31. The baseline's first word clears AVX (CPUID leaf 1 ECX bit 28).
Inspect OpenSSL's effective capability vector with the same environment:

```sh
OPENSSL_ia32cap='~0x0:~0x5f42fc230028:0:0:0' \
  /absolute/path/openssl4/bin/openssl version -a
```

Run only the affected operation, using the resulting benchmark executable
from `--no-run` (or pass these Criterion arguments after `cargo bench --`):

```sh
VG_CPU_FEATURES=bmi2,adx \
OPENSSL_ia32cap='~0x0:~0x5f42fc230028:0:0:0' \
VG_BENCHES=rsa VG_BENCH_RSA_KEYS=/absolute/path/rsa-bench-keys \
  /path/to/primitives-BINARY --bench '^rsa_from_primes/' \
  --warm-up-time 0.3 --measurement-time 1 --sample-size 30 --noplot
```

Keep separate result directories (`CARGO_TARGET_DIR`) for each run, retain
Criterion's raw samples, and interleave baseline and candidate binaries over
multiple rounds. Report absolute times, variability, revisions, build flags,
CPU model, OpenSSL version and the effective masks. Key construction currently
uses the same VG implementation in all three restricted configurations;
CPU dispatch variants of the RSA private operation do not imply variants of
key construction.
