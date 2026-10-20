"""Native i686 experiments; never publishes or certifies unproven code."""
import json, math, os, pathlib, shutil, statistics, subprocess, sys
root=pathlib.Path.cwd(); out=root/'prototype-results';out.mkdir(exist_ok=True)
assert 'i686' in subprocess.check_output(['rustc','-vV'],text=True), 'Native i686 required'
(out/'machine.txt').write_text(subprocess.check_output(['rustc','-vV'],text=True)+subprocess.check_output(['openssl','version','-a'],text=True)+pathlib.Path('/proc/cpuinfo').read_text().split('\n\n')[0])
originals={p:(root/p).read_bytes() for p in ['src/asm/x86/dsa.rs','src/dsa/parameters/tests.rs','src/dsa/tests.rs']}
(root/'.unproven-dsa-experiment').touch()
env=os.environ.copy();env['CARGO_TARGET_DIR']=str(root/'bench-target');env['VG_BENCHES']='dsa'
variants=['baseline','d','w','dw','dwp','dwpr2','dwpr4','dwpr8','dwpr0']
if env.get('PROTOTYPE_VARIANTS'):variants=env['PROTOTYPE_VARIANTS'].split()
if len(sys.argv)>1:variants=sys.argv[1:]
assert all(v.isalnum() and v.isascii() for v in variants), 'Invalid variant name'
def run(cmd,log,extra=None):
    with open(out/log,'w') as f:
        subprocess.run(cmd,env=env| (extra or {}),stdout=f,stderr=subprocess.STDOUT,check=True)
def build(cmd,log):
    run(cmd+['--message-format=json'],log)
    messages=[]
    for line in (out/log).read_text().splitlines():
        try:m=json.loads(line)
        except ValueError:continue
        if m.get('reason')=='compiler-artifact' and m.get('executable'):messages.append(m['executable'])
    assert len(messages)==1,messages
    return messages[0]
for mode in variants:
    for p,b in originals.items():(root/p).write_bytes(b)
    run(['python3','experiments/dsa_x86/install.py',f'experiments/dsa_x86/manifests/{mode}.json.gz','.'],mode+'-install.log')
    test=build(['cargo','test','--release','--lib','--no-run'],mode+'-test-build.log')
    run([test,'dsa::','--nocapture','--test-threads=1'],mode+'-tests.log')
    exe=build(['cargo','bench','--manifest-path','bench/Cargo.toml','--bench','primitives','--no-run'],mode+'-bench-build.log')
    shutil.copy2(exe,out/mode)
    symbols=subprocess.check_output(['nm','-S','--size-sort',exe],text=True)
    (out/(mode+'-code-size.txt')).write_text('\n'.join(line for line in symbols.splitlines() if 'vg_dsa_' in line or 'proto_dsa_' in line)+'\n')
    print('BUILT',mode,flush=True)
for r in range(3):
    order=variants if r%2==0 else list(reversed(variants))
    for mode in order:
        home=out/'criterion'/mode/str(r)
        filt='^dsa_generate_key' if mode=='baseline' else '^dsa_generate_key.*/verified-garbage/'
        run([str(out/mode),'--bench',filt,'--warm-up-time','0.1','--measurement-time','0.3','--sample-size','25','--noplot'],f'{mode}-round{r}.log',{'CRITERION_HOME':str(home)})
        print('MEASURED',mode,r,flush=True)
rows={}
for mode in variants:
    rows[mode]={}
    for p in (out/'criterion'/mode).rglob('new/estimates.json'):
        key='/'.join(p.relative_to(out/'criterion'/mode).parts[1:-2])
        rows[mode].setdefault(key,[]).append(json.loads(p.read_text())['median']['point_estimate'])
assert rows and all(rows.values()),'No criterion estimates found'
summary=['| Variant | Workload | median of round medians (ms) | round medians (ms) |','|---|---|---:|---|']
for mode,data in rows.items():
    for key,v in sorted(data.items()):summary.append(f'| {mode} | {key} | {statistics.median(v)/1e6:.4f} | '+', '.join(f'{x/1e6:.4f}' for x in v)+' |')
summary+=['','Fixed CAVP parameter searches, three repetitions per width:','| Variant | Bits | median ms | samples ms |','|---|---:|---:|---|']
for mode in variants:
    times={}
    for line in (out/(mode+'-tests.log')).read_text().splitlines():
        if 'FIXED_PARAM ' in line:
            bits,ns=line.split('FIXED_PARAM ')[1].split();times.setdefault(bits,[]).append(int(ns)/1e6)
    for bits,v in times.items():summary.append(f'| {mode} | {bits} | {statistics.median(v):.3f} | '+', '.join(f'{x:.3f}' for x in v)+' |')
(out/'summary.md').write_text('\n'.join(summary)+'\n');(out/'raw.json').write_text(json.dumps(rows,indent=2))
print('\n'.join(summary),flush=True)
if 'GITHUB_STEP_SUMMARY' in env:
    with open(env['GITHUB_STEP_SUMMARY'],'a') as f:f.write('\n'.join(summary)+'\n')
if env.get('PROTOTYPE_PARAMETERS')=='1':
    fixed={}
    for mode in variants:
        times={}
        for line in (out/(mode+'-tests.log')).read_text().splitlines():
            if 'FIXED_PARAM ' in line:
                bits,ns=line.split('FIXED_PARAM ')[1].split();times.setdefault(bits,[]).append(int(ns))
        fixed[mode]={bits:statistics.median(v) for bits,v in times.items()}
    winner=min((v for v in variants if v!='baseline'),key=lambda v:sum(math.log(ns/fixed['baseline'][bits]) for bits,ns in fixed[v].items()))
    print('PARAMETER_WINNER',winner,flush=True)
    for mode in ['baseline',winner]:
        filt='^dsa_generate_parameters/openssl/' if mode=='baseline' else '^dsa_generate_parameters/verified-garbage/'
        run([str(out/mode),'--bench',filt,'--warm-up-time','0.1','--measurement-time','0.3','--sample-size','10','--noplot'],mode+'-random-parameters.log',{'VG_BENCHES':'dsa_parameters','CRITERION_HOME':str(out/'parameters'/mode)})
    lines=['','Complete random parameter generation (10 samples; search variance applies):','| Variant | Workload | median ms |','|---|---|---:|']
    for mode in ['baseline',winner]:
        for p in sorted((out/'parameters'/mode).rglob('new/estimates.json')):
            key='/'.join(p.relative_to(out/'parameters'/mode).parts[:-2])
            ns=json.loads(p.read_text())['median']['point_estimate']
            lines.append(f'| {mode} | {key} | {ns/1e6:.3f} |')
    with (out/'summary.md').open('a') as f:f.write('\n'.join(lines)+'\n')
    print('\n'.join(lines),flush=True)
    if 'GITHUB_STEP_SUMMARY' in env:
        with open(env['GITHUB_STEP_SUMMARY'],'a') as f:f.write('\n'.join(lines)+'\n')
for mode in variants:(out/mode).unlink()
