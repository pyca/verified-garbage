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
print('PRIVATE_WINDOW_BASE '+subprocess.check_output(['git','rev-parse','HEAD'],cwd=base,text=True).strip(),flush=True)
os.environ['VG_BENCH_MODULES']='rsa'
os.environ.pop('VG_CPU_FEATURES',None)
original=b.stage
mode='base'
def stage(checkout,bench=None):
 r=original(checkout,bench)
 payload=head/'ci/private_window_experiment'
 if mode!='base': shutil.copy2(payload/f'{mode}.rs',b.STAGE/'src/asm/aarch64/rsa.rs')
 for bits in [2048,3072,4096]:shutil.copy2(payload/f'crt-{bits}.pem',b.STAGE/'bench'/f'crt-{bits}.pem')
 for module in ['rsa','rsa_pss','rsa_oaep']:
  p=b.STAGE/f'bench/benches/primitives/{module}.rs'
  replacement='Rsa::private_key_from_pem(&std::fs::read(format!("'+str(b.STAGE)+'/bench/crt-{bits}.pem")).unwrap()).unwrap()'
  p.write_text(p.read_text().replace('Rsa::generate(bits).unwrap()',replacement))
 return r
b.stage=stage
root=Path('private-window-results').resolve();root.mkdir(exist_ok=True)
modes=['base','holes_trim','holes_trim8'];bins={}
for mode in modes:
 dest=root/f'bench-{mode}';shutil.copy2(b.build(base),dest);bins[mode]=dest
 subprocess.run([str(dest),'--test','^rsa_(private|pss_sha256_mgf1_sha256_sign|oaep_sha256_mgf1_sha256_decrypt)/'],check=True)
env=dict(os.environ,CRITERION_HOME=str(root/'criterion'))
groups='rsa_private'
for i,order in enumerate([modes,list(reversed(modes)),modes[2:]+modes[:2]],1):
 for mode in order+['reference']:
  lib='(openssl|aws-lc-rs)' if mode=='reference' else 'verified-garbage'
  binary=bins['base'] if mode=='reference' else bins[mode]
  print(f'PRIVATE_WINDOW round {i} {mode}',flush=True)
  subprocess.run([str(binary),'--bench',f'^{groups}/{lib}/(256|384|512)$','--noplot','--warm-up-time','0.5','--measurement-time','2','--sample-size','40','--nresamples','1000','--save-baseline',f'{mode}-{i}'],env=env,check=True)
rows=[]
for est in sorted((root/'criterion').glob('*/*/*/*/estimates.json')):
 rel=est.relative_to(root/'criterion');row=dict(operation=rel.parts[0],library=rel.parts[1],bytes=int(rel.parts[2]),run=rel.parts[3],estimates=json.loads(est.read_text()),samples=json.loads((est.parent/'sample.json').read_text()))
 if row['run']=='new':continue
 rows.append(row);print('PRIVATE_WINDOW_SAMPLE '+json.dumps(row),flush=True)
(root/'results.json').write_text(json.dumps(rows,indent=2))
