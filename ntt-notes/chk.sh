for nm in $*; do aarch64-linux-gnu-gcc -O1 -static t.c p_$nm.s -o t2 && echo $nm $(qemu-aarch64 ./t2 | tail -1)
for n in my_fwd my_inv; do awk "/^$n:/{f=1;next} /^ret/{f=0} f" p_$nm.s | grep -v adrp | sed 's/:lo12:[a-z_]*/0/' > $n.2.s
for c in neoverse-n1 neoverse-n2 neoverse-v1 neoverse-v2 apple-m1; do echo -n "$n $c "; llvm-mca-18 -mtriple=aarch64 -mcpu=$c -iterations=50 $n.2.s 2>&1 | grep -E "Total Cycles|error" | head -1| awk '{printf "%d  ", $3/50}'; done; echo; done; done
