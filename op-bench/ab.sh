#!/bin/sh
# A/B of whole private ops: main's CRT (rsa_base.rs), the 5-bit window (rsa_w5.rs)
# the 4-bit window with the AVX2 selection (rsa_w4v.rs), and the 5-bit window with the AVX2 selection (src/asm/x86_64/rsa.rs as committed).
set -e
cd "$(dirname "$0")"
R=../src/asm/x86_64/rsa.rs
cp $R /tmp/rsa_w5v.rs
cargo build --release -q && cp target/release/op-bench /tmp/op_w5v
cp rsa_w5.rs $R && cargo build --release -q && cp target/release/op-bench /tmp/op_w5
cp rsa_w4v.rs $R && cargo build --release -q && cp target/release/op-bench /tmp/op_w4v
cp rsa_base.rs $R && cargo build --release -q && cp target/release/op-bench /tmp/op_base
cp /tmp/rsa_w5v.rs $R
F=${VG_CPU_FEATURES:-$(for f in avx avx2 avx512f bmi1 bmi2 adx; do grep -qw $f /proc/cpuinfo && printf "%s," $f; done | sed "s/,$//")}
for i in $(seq ${ROUNDS:-3}); do for v in base w4v w5 w5v; do
  VG_CPU_FEATURES=$F OPENSSL_ia32cap="~0x0:~0x200000" ${PIN:-} /tmp/op_$v | sed "s/^/op $v /"
done; done
