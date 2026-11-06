# Declaration graph from the build's .ilean files.
# Output: decl_mod (decl -> module, decls with a range), edges (decl -> set of
# referenced constants), modcmd (module -> constants referenced outside any
# declaration), cmod (constant -> defining module), ranges (decl -> range).
import json, os, sys, pickle
LEAN = os.environ.get('REPO', os.getcwd()) + '/lean/'
root = LEAN + '.lake/build/lib/lean'
out = sys.argv[1]
decl_mod, edges, modcmd, cmod, ranges, srcmod = {}, {}, {}, {}, {}, {}
for top in ('VerifiedGarbage', 'VerifiedGarbageTest'):
    for dp, _, fs in os.walk(os.path.join(root, top)):
        for f in fs:
            if not f.endswith('.ilean'): continue
            rel = os.path.relpath(os.path.join(dp, f[:-6] + '.lean'), root)
            if not os.path.exists(LEAN + rel): continue
            d = json.load(open(os.path.join(dp, f)))
            m = d['module']
            modcmd.setdefault(m, set())
            for n, r in d.get('decls', {}).items():
                decl_mod[n] = m; edges.setdefault(n, set()); ranges[n] = r
            for k, v in d['references'].items():
                kk = json.loads(k)
                if 'c' not in kk: continue
                c = kk['c']['n']; cmod.setdefault(c, kk['c']['m'])
                for u in v.get('usages', []):
                    src = u[4] if len(u) > 4 else None
                    if src: edges.setdefault(src, set()).add(c); srcmod.setdefault(src, m)
                    else: modcmd[m].add(c)
# an edge whose source is no declaration (an `example`, an auxiliary name
# with no declaration above it) counts as a module-level reference
nodes = set(decl_mod)
for src in list(edges):
    if src in nodes: continue
    c = src
    while c not in nodes and '.' in c: c = c.rsplit('.', 1)[0]
    if c not in nodes:
        modcmd.setdefault(srcmod[src], set()).update(edges.pop(src))
pickle.dump((decl_mod, edges, modcmd, cmod, ranges), open(out, 'wb'))
print(len(decl_mod), sum(len(e) for e in edges.values()))
