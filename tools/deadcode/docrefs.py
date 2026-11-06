# Backticked names in the tree that name a removed declaration: by a name no
# remaining declaration shares, or by a short name removed from the file
# itself or a module it imports (with no remaining one of that name there).
# usage: docrefs.py graph.pkl live.pkl plan.pkl
import pickle, os, re, sys
from collections import defaultdict
dm = pickle.load(open(sys.argv[1], 'rb'))[0]
I = pickle.load(open(sys.argv[2], 'rb'))[5]
C, g = pickle.load(open(sys.argv[3], 'rb'))
LEAN = os.environ.get('REPO', os.getcwd()) + '/lean/'
tick = re.compile(r'`([^`]+)`')
word = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")
remaining = set(dm) - C
tail = lambda d, k: '.'.join(d.split('.')[-k:])
short = defaultdict(set)
for d in C:
    for k in (1, 2): short[tail(d, k)].add(d)
remshort = {tail(d, k) for d in remaining for k in (1, 2)}
bym = defaultdict(set)
for d, m in dm.items(): bym[m].add(d)
out = set()
for m, ims in I.items():
    p = LEAN + m.replace('.', '/') + '.lean'
    if not os.path.exists(p): continue
    rem, keep = defaultdict(set), set()
    for x in [m] + list(ims):
        for d in bym.get(x, ()):
            (rem[tail(d, 1)].add(d) if d in C else keep.add(tail(d, 1)))
    for i, l in enumerate(open(p).read().split('\n')):
        for t in tick.findall(l):
            for w in word.findall(t):
                k = next((k for k in (w, tail(w, 2)) if k in short and k not in remshort), None)
                s = tail(w, 1)
                if k: out.add((os.path.relpath(p, LEAN), i + 1, w, sorted(short[k])[0]))
                elif s in rem and s not in keep: out.add((os.path.relpath(p, LEAN), i + 1, w, sorted(rem[s])[0]))
for f, i, w, d in sorted(out): print(f'{f}:{i}: {w} ({d})')
