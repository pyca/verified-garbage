"""UNPROVED experiment only: native lifetime A/B, no Lean or full benchmark build."""
from pathlib import Path
import hashlib, json, os, shutil, statistics, subprocess
root=Path.cwd()
base=root/'base';head=root/'head';out=root/'lifetime-results';out.mkdir()
harness=head/'examples/mldsa-cache-lifetime.rs'
(base/'examples').mkdir(exist_ok=True)
shutil.copy2(harness,base/'examples/mldsa-cache-lifetime.rs')
subprocess.run(['rustc','-Vv'],check=True)
for repo in (base,head):
 print(repo,subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),flush=True)
print('logical CPUs',os.cpu_count(),'affinity',len(os.sched_getaffinity(0)) if hasattr(os,'sched_getaffinity') else 'unknown',flush=True)
policies=['baseline','2']
for policy in policies:
 repo=base if policy=='baseline' else head
 with (out/f'build-{policy}.log').open('w') as log:
  subprocess.run(['cargo','build','--release','--features','cpu-features-env','--example','mldsa-cache-lifetime'],cwd=repo,env=dict(os.environ,VG_MLDSA_CACHE_AFTER=policy),stdout=log,stderr=subprocess.STDOUT,check=True)
 shutil.copy2(repo/'target/release/examples/mldsa-cache-lifetime',out/f'run-{policy}')
 print('built',policy,flush=True)
results={}
for run,order in enumerate([policies,list(reversed(policies)),policies]):
 for policy in order:
  p=subprocess.run([str(out/f'run-{policy}')],capture_output=True,text=True,check=True, env=dict(os.environ, VG_MLDSA_THREADS_ONLY='1', VG_MLDSA_THREAD_OPS='512', VG_MLDSA_PIN_CORES=','.join(map(str,sorted(os.sched_getaffinity(0))[:4]))))
  (out/f'results-{run}-{policy}.csv').write_text(p.stdout)
  (out/f'stderr-{run}-{policy}.log').write_text(p.stderr)
  for line in p.stdout.splitlines():
   cells=line.split(',')
   if cells[0] in ('life','threads4'):
    key=','.join(cells[:4]);results.setdefault(key,{}).setdefault(policy,[]).append(float(cells[4]))
  print(run,policy,'complete',flush=True)
summary={k:{p:{'median_us':statistics.median(v),'runs_us':v} for p,v in by.items()} for k,by in results.items()}
(out/'summary.json').write_text(json.dumps(summary,indent=2))
(out/'binaries.json').write_text(json.dumps({p:hashlib.sha256((out/f'run-{p}').read_bytes()).hexdigest() for p in policies},indent=2))
lines=['## UNPROVED ML-DSA automatic-cache lifetime experiment','',
'Full key construction, operations and drop. Controlled concurrency follow-up only: four pinned worker cores, 512 operations per worker, 12 fixed-key samples, three interleaved passes. Previous short lifetime and concurrency results remain separate. Signing uses deterministic signing, verification uses valid signatures. Four-thread cases include gate overhead and report throughput, not latency; logical CPU and affinity counts are logged.','',
'| Set | Operation | Uses | Baseline µs | Auto second use µs | Latency reduction |',
'|---|---|---:|---:|---:|---:|']
for key,by in summary.items():
 if not key.startswith('life,'):continue
 _,n,op,count=key.split(',');b=by['baseline']['median_us'];c=by['2']['median_us']
 lines.append(f'| {n} | {op} | {count} | {b:.3f} | {c:.3f} | {(1-c/b)*100:.2f}% |')
report='\n'.join(lines)+'\n';print(report,flush=True)
with open(os.environ['GITHUB_STEP_SUMMARY'],'a') as f:f.write(report)

# The unchanged workflow already saves this Criterion-shaped artifact path.
archive=root/'bench-compare/auto-lifetime/new'
archive.mkdir(parents=True,exist_ok=True)
(archive/'measurements.json').write_text(json.dumps({
 'summary':summary,
 'files':{p.name:p.read_text() for p in out.iterdir() if p.suffix in ('.csv','.json','.log')},
},indent=2))
