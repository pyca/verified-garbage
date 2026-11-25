python3 gen.py 2>/dev/null
for n in my_fwd my_inv; do
awk "/^$n:/{f=1;next} /^ret/{f=0} f" p.s | grep -v adrp | sed 's/:lo12:[a-z_]*/0/' > $n.mca.s
for c in neoverse-n1 neoverse-n2 neoverse-v1 neoverse-v2 apple-m1; do llvm-mca-18 -mtriple=aarch64 -mcpu=$c -iterations=50 $n.mca.s 2>&1 | grep -E "Total Cycles|error" | head -1| sed "s/^/$n $c /"; done; done
