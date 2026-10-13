# UNPROVED scheduling experiment. Native AArch64 only; never merge.
import sys,os,json,shutil,subprocess,statistics,pathlib
from pathlib import Path
import bench_compare_production as b
def prepare_openssl4():
    import tempfile
    root = pathlib.Path(tempfile.mkdtemp(prefix="vg-openssl4-"))
    source, prefix = root / "source", root / "install"
    rev = "af1775b60dfa141a4ad762585052cabeb9f37e9e"
    subprocess.run(["git", "clone", "--depth", "1", "--branch", "openssl-4.0.3",
                    "https://github.com/openssl/openssl.git", str(source)], check=True)
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()
    if actual != rev:
        raise RuntimeError("OpenSSL tag no longer matches pinned source revision")
    with (root / "build.log").open("w") as log:
        for command in [["./Configure", "linux-aarch64", "--prefix=" + str(prefix), "--libdir=lib", "no-shared", "no-tests", "no-docs"],
                        ["make", "-j4"], ["make", "install_sw"]]:
            result = subprocess.run(command, cwd=source, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                log.flush()
                print((root / "build.log").read_text()[-20000:], flush=True)
                result.check_returncode()
    os.environ["OPENSSL_DIR"] = str(prefix)
    os.environ["OPENSSL_STATIC"] = "1"
    os.environ["PATH"] = str(prefix / "bin") + os.pathsep + os.environ["PATH"]
    print("RSA_GAP_OPENSSL_SOURCE " + rev, flush=True)
    subprocess.run([str(prefix / "bin/openssl"), "version", "-a"], check=True)


base,head=Path(sys.argv[1]).resolve(),Path(sys.argv[2]).resolve()
prepare_openssl4()
subprocess.run(['rustc','-Vv'],check=True)
print('RSA_EXPERIMENT_BASE '+subprocess.check_output(['git','rev-parse','HEAD'],cwd=base,text=True).strip(),flush=True)
print('RSA_EXPERIMENT_HEAD '+subprocess.check_output(['git','rev-parse','HEAD'],cwd=head,text=True).strip(),flush=True)
os.environ['VG_BENCH_MODULES']='rsa'
os.environ.pop('VG_CPU_FEATURES',None)
original=b.stage
mode='base'
def stage(checkout,bench=None):
 r=original(checkout,bench)
 if mode!='base': shutil.copy2(head/'ci/rsa_reduction_experiment'/f'{mode}.rs',b.STAGE/'src/asm/aarch64/rsa.rs')
 return r
b.stage=stage
root=Path('rsa-reduction-results').resolve();root.mkdir(exist_ok=True)
modes=['base','diag'];bins={}
for mode in modes:
 binary=b.build(base)
 dest=root/f'bench-{mode}';shutil.copy2(binary,dest);bins[mode]=dest
# All compilation is complete before timing. Same benchmark source and stage path.
env=dict(os.environ,CRITERION_HOME=str(root/'criterion'))
rows=[]
for i,order in enumerate([modes,list(reversed(modes)),modes],1):
 for mode in order:
  print(f'RSA_EXPERIMENT round {i} {mode}',flush=True)
  subprocess.run([str(bins[mode]),'--bench','^rsa_(public|private)/verified-garbage/(256|384|512)$','--noplot','--warm-up-time','1','--measurement-time','3','--sample-size','50','--nresamples','1000','--save-baseline',f'{mode}-{i}'],env=env,check=True)
 for lib in ['openssl']:
  subprocess.run([str(bins['base']),'--bench',f'^rsa_(public|private)/{lib}/(256|384|512)$','--noplot','--warm-up-time','1','--measurement-time','3','--sample-size','50','--nresamples','1000','--save-baseline',f'reference-{i}'],env=env,check=True)
for op in ['rsa_public','rsa_private']:
 for n in [256,384,512]:
  vals={}
  for mode in modes+['openssl']:
   lib='openssl' if mode=='openssl' else 'verified-garbage'
   prefix='reference' if mode=='openssl' else mode
   vals[mode]=[]
   for i in [1,2,3]:
    folder=root/'criterion'/op/lib/str(n)/f'{prefix}-{i}'
    estimates=json.loads((folder/'estimates.json').read_text())
    vals[mode].append(estimates['mean']['point_estimate']/1000)
    print('RSA_REDUCTION_SAMPLE '+json.dumps(dict(operation=op,bits=n*8,mode=mode,round=i,estimates=estimates,samples=json.loads((folder/'sample.json').read_text()))),flush=True)
  row=dict(operation=op,bits=n*8,us=vals,delta_percent={m:100*(statistics.mean(v)/statistics.mean(vals['base'])-1) for m,v in vals.items()})
  rows.append(row);print('RSA_REDUCTION_RESULT '+json.dumps(row),flush=True)
(root/'results.json').write_text(json.dumps(rows,indent=2))
