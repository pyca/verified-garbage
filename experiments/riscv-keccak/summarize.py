#!/usr/bin/env python3
import csv,json,math,statistics,sys
from collections import defaultdict
from pathlib import Path
path=Path(sys.argv[1]);data=defaultdict(lambda:defaultdict(list));paired=defaultdict(dict)
for r in csv.DictReader(path.open()):
 data[r['workload']][r['variant']].append(float(r['wall_ns']))
 paired[r['workload']][r['variant'],int(r['round'])]=(float(r['wall_ns']),float(r['cpu_ns']))
variants=sorted(set.intersection(*(set(v) for v in data.values()))-{'verified'})
scores={v:math.exp(statistics.mean(math.log(statistics.median(rows[v])/statistics.median(rows['verified'])) for rows in data.values())) for v in variants}
print('| Workload | Variant | Baseline median | Candidate median | Time reduction | Paired wall range | Paired CPU range |')
print('|---|---|---:|---:|---:|---:|---:|')
for work,vs in data.items():
 for v in variants:
  base=statistics.median(vs['verified']);cand=statistics.median(vs[v]);pw=[];pc=[]
  for (name,r),value in paired[work].items():
   if name==v:
    b=paired[work]['verified',r];pw.append(100*(1-value[0]/b[0]));pc.append(100*(1-value[1]/b[1]))
  print(f'| {work} | {v} | {base/1000:.3f} µs | {cand/1000:.3f} µs | {100*(1-cand/base):.2f}% | {min(pw):.2f}% … {max(pw):.2f}% | {min(pc):.2f}% … {max(pc):.2f}% |')
if '--select' in sys.argv:
 chosen=sorted(variants,key=scores.get)[:2]
 (path.parent/'selected.txt').write_text(' '.join(chosen)+'\n')
 (path.parent/'selection.json').write_text(json.dumps({'geometric_mean_ratios':scores,'chosen_for_independent_client_confirmation':chosen},indent=2)+'\n')
 print('\nIndependent client confirmation candidates: '+', '.join(chosen))
