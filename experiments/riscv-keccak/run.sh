#!/bin/sh
set -eu
cd "$(dirname "$0")/../.."
out=experiments/riscv-keccak/out
mkdir -p "$out"
{
 git rev-parse HEAD
 uname -a
 gcc --version
 openssl version -a
 cat /proc/cpuinfo
 nproc
 for path in /sys/fs/cgroup/cpu.max /sys/fs/cgroup/cpu.stat; do
  if [ -f "$path" ]; then echo "$path";cat "$path";fi
 done
} > "$out/machine.txt"
head -n 25 "$out/machine.txt"
python3 experiments/riscv-keccak/generate.py
python3 experiments/riscv-keccak/parity.py
objects=
while IFS= read -r src; do
 obj="${src%.S}.o"
 gcc -O3 -march=rv64gc -mabi=lp64d -c "$src" -o "$obj"
 objects="$objects $obj"
done < "$out/asm-files.txt"
gcc -O3 -std=c11 -march=rv64gc -mabi=lp64d -Wall -Wextra -Werror \
 -Iexperiments/riscv-keccak experiments/riscv-keccak/probe.c \
 "$out/candidates.c" "$out/constants.c" $objects \
 -Wl,--wrap=vg_keccak_f1600 -pthread -lcrypto -o "$out/probe"
objdump -d "$out/probe" > "$out/disassembly.txt"
nm -S --size-sort "$out/probe" > "$out/symbols.txt"
"$out/probe" > "$out/kernels.csv" 2> "$out/checks.txt"
python3 experiments/riscv-keccak/summarize.py "$out/kernels.csv" --select > "$out/kernel-summary.md"
cat "$out/checks.txt"
cat "$out/kernel-summary.md"
# This is a separate process and later measurement phase. Selection is based
# only on the kernel/SHAKE sweep; client times cannot influence the choice.
read -r first second < "$out/selected.txt"
"$out/probe" --clients "$first" "$second" > "$out/clients.csv" 2> "$out/client-checks.txt"
python3 experiments/riscv-keccak/summarize.py "$out/clients.csv" > "$out/client-summary.md"
cat "$out/client-checks.txt"
cat "$out/client-summary.md"
cat "$out/kernels.csv" "$out/clients.csv"

"$out/probe" --threads "$first" "$second" > "$out/threads.csv" 2> "$out/thread-checks.txt"
python3 experiments/riscv-keccak/summarize.py "$out/threads.csv" > "$out/thread-summary.md"
cat "$out/thread-summary.md"
