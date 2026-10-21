import importlib.util,json,pathlib,statistics,types
spec=importlib.util.spec_from_file_location('bench_compare', 'head/ci/bench_compare.py')
bc=importlib.util.module_from_spec(spec);spec.loader.exec_module(bc)
args=types.SimpleNamespace(warm_up_time=.3,measurement_time=1.)
head=pathlib.Path('head').resolve();base=pathlib.Path('base').resolve()
binaries={'head':bc.build(head),'base':bc.build_base(base,head)[0]}
for b in binaries.values():bc.check_arch(b,'x86')
root=pathlib.Path('api-results').resolve();root.mkdir(exist_ok=True)
results={s:{} for s in ['base','head','openssl']}
print('CPU:',bc.cpu_model(),flush=True)
for r in range(3):
    for side in (['base','head','openssl'] if r%2==0 else ['openssl','head','base']):
        lib='openssl' if side=='openssl' else bc.VG
        binary=binaries['head' if side=='openssl' else side]
        times=bc.run(binary,root/f'{side}-{r}',lib,args,head,'rsa',['rsa_from_components','rsa_private'],'rsa')
        for (g,k),t in times.items():
            results[side].setdefault(f'{g}/{k}',[]).append(t)
        print(json.dumps({'round':r,'side':side,'ns':{f'{g}/{k}':t for (g,k),t in times.items()}}),flush=True)
(root/'rounds.json').write_text(json.dumps(results,indent=2))
print('Median of three round medians (ns):',flush=True)
for key in sorted(results['head']):
    t={s:statistics.median(v[key]) for s,v in results.items()}
    print(key,json.dumps(t),'head/base',t['head']/t['base'],'head/OpenSSL',t['head']/t['openssl'],flush=True)
