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
# Each runs alone on CPU $BENCH_CPU (default 2). Linux only (`taskset`).
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
rustls=$here/target/rustls
out=$here/target/bench-results
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
