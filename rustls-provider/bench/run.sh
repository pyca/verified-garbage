#!/bin/sh
# Runs every benchmark RESULTS.md reports, verified-garbage against
# aws-lc-rs, into target/bench-results, and summarizes them:
#
# * rustls-bench, all tests, `rounds` times (default 5) per provider;
# * provider-primitives (each provider's primitives through the rustls
#   traits), three times;
# * aws-lc-compare (each library's primitives through its own API), three
#   times, and its AEAD size sweep.
#
# Each runs alone on CPU $BENCH_CPU (default 2), writing into $BENCH_OUT
# (default target/bench-results). Linux only (`taskset`).
#
# To measure an older CPU class on a newer x86-64 machine, restrict both
# libraries' CPU features: verified-garbage's with VG_CPU_FEATURES (the
# benchmarks build it with `cpu-features-env`), aws-lc's with
# OPENSSL_ia32cap. For a Cascade Lake class (AVX-512F/BW/VL and ADX, but no
# IFMA, VAES, VPCLMULQDQ or SHA-NI):
#
#   VG_CPU_FEATURES=avx,avx2,avx512f,avx512bw,avx512vl,bmi1,bmi2,adx,aes,pclmulqdq,ssse3 \
#   OPENSSL_ia32cap='~0x0:~0x574220200000' BENCH_OUT=target/bench-results-clx bench/run.sh
#
# The second OPENSSL_ia32cap word masks CPUID leaf 7: EBX (low half) bits 21
# (AVX512IFMA) and 29 (SHA), ECX (high half) bits 1 (AVX512VBMI),
# 6 (AVX512VBMI2), 8 (GFNI), 9 (VAES), 10 (VPCLMULQDQ), 12 (AVX512BITALG)
# and 14 (AVX512VPOPCNTDQ).
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
rustls=$here/target/rustls
out=${BENCH_OUT:-$here/target/bench-results}
cpu=${BENCH_CPU:-2}
rounds=${1:-5}

[ -d "$rustls" ] || "$here/bench/setup-rustls.sh" "$rustls"
(cd "$rustls" && cargo build --profile=bench -p rustls-bench --features aws-lc-rs,verified-garbage)
(cd "$here/bench/aws-lc-compare" && cargo build --release)
compare=$here/bench/aws-lc-compare/target/release/aws-lc-compare

mkdir -p "$out"
for bits in 2048 3072 4096; do
    [ -f "$out/rsa$bits.der" ] ||
        openssl genrsa -traditional "$bits" 2>/dev/null |
        openssl rsa -traditional -outform DER -out "$out/rsa$bits.der" 2>/dev/null
done

for r in $(seq 1 "$rounds"); do
    for p in aws-lc-rs verified-garbage; do
        echo "rustls-bench $p, round $r" >&2
        taskset -c "$cpu" "$rustls/target/release/rustls-bench" --provider "$p" --api buffered \
            > "$out/all-$p-$r.tsv"
    done
done
for r in 1 2 3; do
    echo "provider-primitives, round $r" >&2
    taskset -c "$cpu" "$rustls/target/release/provider-primitives" > "$out/primitives-$r.txt"
    echo "aws-lc-compare, round $r" >&2
    taskset -c "$cpu" "$compare" "$out" > "$out/aws-lc-compare-$r.txt"
    taskset -c "$cpu" "$compare" "$out" sweep > "$out/sweep-$r.txt"
done

python3 "$here/bench/summarize.py" "$out" | tee "$out/summary.txt"
