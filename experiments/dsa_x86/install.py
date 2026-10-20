"""Install Lean-rendered UNPROVEN bodies into a disposable checkout only."""
import argparse,json,re,gzip
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('manifest');p.add_argument('checkout');a=p.parse_args()
root=Path(a.checkout).resolve()
if not (root/'.unproven-dsa-experiment').exists():
    raise SystemExit('Refusing a checkout without .unproven-dsa-experiment marker')
path=root/'src/asm/x86/dsa.rs';s=path.read_text()
pattern=re.compile(r'(#\[unsafe\(naked\)\]\npub\(crate\) unsafe extern "C" fn (\w+)\([^\n]+\) [^{]*\{).*?\n\}',re.S)
functions={m[2]:m for m in pattern.finditer(s)}
bindings=dict(re.findall(r'(\w+) = sym ([^,]+),',s))
bindings['vg_rsa_mont_mul_at']='super::rsa_mont::vg_rsa_mont_mul_at'
replacements={};extra=[]
manifest=json.loads(gzip.decompress(Path(a.manifest).read_bytes()) if a.manifest.endswith('.gz') else Path(a.manifest).read_bytes())
manifest+=json.loads(gzip.decompress((root/'experiments/dsa_x86/manifests/abi.json.gz').read_bytes()))
for f in manifest:
    name=f['name']; original=name
    if name=='proto_dsa_derive_prevalidated':original='vg_dsa_derive_key'
    elif name.endswith('_public'):original=name[:-7]
    elif name.startswith('proto_dsa_abi_'):original=name.replace('proto_dsa_abi_', 'vg_dsa_')
    signature=functions[original][1].replace(original,name)
    if name.startswith('proto_dsa_abi_'):signature=signature.replace(') {', ') -> u32 {')
    calls=[]
    for call in f['calls']:
        target=bindings.get(call,'super::dsa::'+call)
        calls.append('        '+call+' = sym '+target+',')
    body=signature+'\n    core::arch::naked_asm!(\n        r"'+f['assembly']+'",\n'+'\n'.join(calls)+'\n    )\n}'
    if name in functions:replacements[name]=body
    else:extra.append(body)
s=pattern.sub(lambda m:replacements.get(m[2],m[0]),s)
path.write_text('// UNPROVEN PERFORMANCE EXPERIMENT. NOT FOR RELEASE. Generated from Prototype.lean.\n'+s+'\n'+'\n'.join(extra)+'\n')
print('Installed',len(replacements),'replacements and',len(extra),'internal helpers')

# The same published CAVP tapes, three repetitions, on every candidate.
test=root/'src/dsa/parameters/tests.rs'
t=('extern crate std;\n'+test.read_text()).replace('struct Vector {', '#[derive(Clone)]\nstruct Vector {')
t=t.replace('for v in prime_vectors() {', 'for v in prime_vectors().into_iter().cycle().take(9) {\n        let started = std::time::Instant::now();')
t=t.replace('assert_eq!(tape, 3);', 'std::eprintln!("FIXED_PARAM {} {}", v.bits, started.elapsed().as_nanos());\n        assert_eq!(tape, 3);')
test.write_text(t)

with (root/'src/dsa/tests.rs').open('a') as f:
    f.write('\n'+(root/'experiments/dsa_x86/power_tests.rs').read_text())
