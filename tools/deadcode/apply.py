# Remove the planned declarations: trim modules, delete the emptied ones.
import pickle, os, json, re
from collections import defaultdict
import subprocess, sys
# The ranges are those of the graph's build: apply to an unmodified tree only.
if subprocess.run(['git', '-C', os.environ.get('REPO', os.getcwd()), 'status', '--porcelain', 'lean/'],
                  capture_output=True, text=True).stdout.strip():
    sys.exit('lean/ has changes: apply.py needs the tree the graph was built from')
S = os.environ.get('WORK', '.') + '/'
LEAN = os.environ.get('REPO', os.getcwd()) + '/lean/'
decl_mod, edges, modcmd, cmod, ranges = pickle.load(open(S + os.environ.get('GRAPH', 'g_head.pkl'), 'rb'))
C, gone = pickle.load(open(S + 'plan.pkl', 'rb'))
bymod = defaultdict(set)
for d in C: bymod[decl_mod[d]].add(d)
report = {}
for m, ds in sorted(bymod.items()):
    path = LEAN + m.replace('.', '/') + '.lean'
    if m in gone:
        os.remove(path); report[m] = ('deleted', len(ds)); continue
    mine = {n: r for n, r in ranges.items() if decl_mod[n] == m}
    rm = [(mine[d][0], mine[d][2], d) for d in ds]
    kept = [(a, b) for n, (a, _, b, *_) in mine.items() if n not in ds]
    lines = open(path).read().split('\n')
    drop = set()
    for a, b, d in rm:
        if any(ka <= a and b <= kb and (ka, kb) != (a, b) for ka, kb in kept):
            print('nested in kept, skip', d); continue
        drop.update(range(a, b + 1))
        if b + 1 < len(lines) and not lines[b + 1].strip(): drop.add(b + 1)
    open(path, 'w').write('\n'.join(l for i, l in enumerate(lines) if i not in drop))
    report[m] = ('trimmed', len(ds))
for m in gone - set(bymod):
    os.remove(LEAN + m.replace('.', '/') + '.lean'); report[m] = ('deleted', 0)
# drop the imports of deleted modules everywhere
pat = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(' + '|'.join(re.escape(m) for m in gone) + r')\s*(?:--.*)?$')
for top in ('VerifiedGarbage', 'VerifiedGarbageTest'):
    for dp, _, fs in os.walk(LEAN + top):
        for f in fs:
            if not f.endswith('.lean'): continue
            p = os.path.join(dp, f); t = open(p).read().split('\n')
            k = [l for l in t if not pat.match(l)]
            if len(k) != len(t): open(p, 'w').write('\n'.join(k))
for f in os.listdir(LEAN):
    if f.endswith('.lean'):
        t = open(LEAN + f).read().split('\n'); k = [l for l in t if not pat.match(l)]
        if len(k) != len(t): open(LEAN + f, 'w').write('\n'.join(k)); print('top-level file edited', f)
pickle.dump(report, open(S + 'report.pkl', 'wb'))
print(sum(1 for v in report.values() if v[0] == 'deleted'), 'deleted;', sum(1 for v in report.values() if v[0] == 'trimmed'), 'trimmed')
