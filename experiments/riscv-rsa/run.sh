#!/bin/sh
set -eu
cd "$(dirname "$0")/../.."
mkdir -p experiments/riscv-rsa/out
out=experiments/riscv-rsa/out
{
  git rev-parse HEAD
  uname -a
  gcc --version
  openssl version -a
  cat /proc/cpuinfo
} > "$out/machine.txt"
python3 experiments/riscv-rsa/prepare.py
for name in base pair one two column micro; do
  gcc -O3 -march=rv64gc -mabi=lp64d -c "$out/$name.S" -o "$out/$name.o"
done
gcc -O3 -march=rv64gc -mabi=lp64d -Wall -Wextra -Werror -Wno-misleading-indentation \
  experiments/riscv-rsa/probe.c experiments/riscv-rsa/kernels.c \
  "$out/base.o" "$out/pair.o" "$out/one.o" "$out/two.o" "$out/column.o" "$out/micro.o" \
  -pthread -lcrypto -o "$out/probe"
objdump -d "$out/probe" > "$out/disassembly.txt"
"$out/probe" > "$out/timings.csv" 2> "$out/checks.txt"
python3 experiments/riscv-rsa/summarize.py "$out/timings.csv" > "$out/summary.md"
cat "$out/checks.txt" "$out/summary.md"
