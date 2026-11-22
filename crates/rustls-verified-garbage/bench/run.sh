#!/bin/sh
# Runs rustls-bench's whole suite with each provider, aws-lc-rs and
# verified-garbage, `rounds` times (default 5), alone on CPU $BENCH_CPU
# (default 2), into $BENCH_OUT (default target/bench-results), and writes
# the results there as a results file of ci/bench_report.py's format,
# rustls-bench.json (bench/results.py), which `python3 ci/bench_report.py
# html` charts. Linux only (`taskset`).
#
# To measure an older CPU class on a newer x86-64 machine, restrict both
# libraries' CPU features: verified-garbage's with VG_CPU_FEATURES (the
# benchmarks build it with `cpu-features-env`), aws-lc's with
# OPENSSL_ia32cap. For a Cascade Lake class (AVX-512F/BW/VL and ADX, but no
# IFMA, VAES, VPCLMULQDQ or SHA-NI):
#
#   VG_CPU_FEATURES=avx,avx2,avx512f,avx512bw,avx512vl,bmi1,bmi2,adx,aes,pclmulqdq,ssse3 \
#   OPENSSL_ia32cap='~0x0:~0x574220200000' BENCH_OUT=target/bench-results-clx crates/rustls-verified-garbage/bench/run.sh
#
# The second OPENSSL_ia32cap word masks CPUID leaf 7: EBX (low half) bits 21
# (AVX512IFMA) and 29 (SHA), ECX (high half) bits 1 (AVX512VBMI),
# 6 (AVX512VBMI2), 8 (GFNI), 9 (VAES), 10 (VPCLMULQDQ), 12 (AVX512BITALG)
# and 14 (AVX512VPOPCNTDQ).
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
rustls=$here/../../target/rustls
out=${BENCH_OUT:-$here/../../target/bench-results}
cpu=${BENCH_CPU:-2}
rounds=${1:-5}

[ -d "$rustls" ] || "$here/rustls/setup.sh" "$rustls"
(cd "$rustls" && cargo build --profile=bench -p rustls-bench --features aws-lc-rs,verified-garbage)

mkdir -p "$out"
for r in $(seq 1 "$rounds"); do
    for p in aws-lc-rs verified-garbage; do
        echo "rustls-bench $p, round $r" >&2
        taskset -c "$cpu" "$rustls/target/release/rustls-bench" --provider "$p" --api buffered \
            > "$out/rustls-bench-$p-$r.tsv"
    done
done
python3 "$here/bench/results.py" "$out"
