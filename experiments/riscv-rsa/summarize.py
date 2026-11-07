#!/usr/bin/env python3
import csv,statistics,sys
from collections import defaultdict
rows=list(csv.DictReader(open(sys.argv[1])))
groups=defaultdict(dict)
for r in rows:
    groups[r['workload'],r['variant'],int(r['bits']),int(r['threads'])][int(r['round'])]=float(r['seconds'])/int(r['iterations'])
print('# Native RISC-V RSA experiments\n')
print('Seven alternating-order rounds; elapsed time per operation. Positive delta means faster. Full raw samples accompany this table.\n')
print('| Workload | Variant | Bits | Threads | Median µs/op | Paired time reduction, median [min, max] |')
print('|---|---|---:|---:|---:|---:|')
for (work,v,bits,threads),samples in sorted(groups.items()):
    base='base' if work in ('rsa','public') else 'base_square' if 'square' in v else 'base_mont'
    bs=groups[work,base,bits,threads]
    deltas=[100*(bs[r]-s)/bs[r] for r,s in samples.items()]
    print(f'| {work} | {v} | {bits} | {threads} | {statistics.median(samples.values())*1e6:.2f} | {statistics.median(deltas):+.2f}% [{min(deltas):+.2f}, {max(deltas):+.2f}] |')
print('\nThe C one-row control and C two-row candidate share the same call wrapper. Comparing them isolates the row-fusion idea better than comparing either directly with the emitted inline baseline. C column squaring also includes a call wrapper. No result is a formal proof or a complete constant-time audit.')
