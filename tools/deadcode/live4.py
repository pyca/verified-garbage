# Live set from the roots, conservative about implicit uses.
# usage: live4.py graph.pkl out.pkl [gone.pkl]
# live4: as live3, but an attribute that only sets how a definition unfolds or
# compiles (`irreducible`, `inline`, ...) is no implicit use, and (1) every module-level command of a module the roots
# import counts (`materialize_code`, `materialize_shared`, `taint_summary`
# define what `rw_lit` and `taint_decide` find by name, with no reference);
# (2) with gone.pkl (a plan's (C, gone)), the modules it deletes are left out:
# their declarations, and the imports of them.
# Roots: every declaration of Artifacts/, Generic/, Variants/, TCB/, the tests,
# lakefile-named modules and modules the top-level Lean files import.
# Implicit uses: a declaration with an attribute (`@[...]`, `instance`,
# `attribute [...] x`) in a module the roots import (transitively) is live,
# since simp sets, instances and the like are used without a reference.
# A module-level command's references are live once its module is used.
import pickle, sys, re, os
from collections import defaultdict
decl_mod, edges, modcmd, cmod, ranges = pickle.load(open(sys.argv[1], 'rb'))
GONE = pickle.load(open(sys.argv[3], 'rb'))[1] if len(sys.argv) > 3 else set()
if GONE:
    decl_mod = {d: m for d, m in decl_mod.items() if m not in GONE}
    modcmd = {m: v for m, v in modcmd.items() if m not in GONE}
LEAN = os.environ.get('SRC', os.environ.get('REPO', os.getcwd())) + '/lean/'  # SRC: a checkout of the graph's revision
nodes = set(decl_mod)
def norm(c):
    o = c
    while c not in nodes and '.' in c: c = c.rsplit('.', 1)[0]
    return c if c in nodes else None
E = defaultdict(set)
for d, cs in edges.items():
    p = d if d in nodes else norm(d)
    if p is None: continue
    E[p] |= cs
ROOTPRE = ('VerifiedGarbage.Artifacts.', 'VerifiedGarbage.Generic.', 'VerifiedGarbage.Variants.',
           'VerifiedGarbage.TCB.', 'VerifiedGarbageTest.')
extra = set()
lf = open(LEAN + 'lakefile.toml').read()
for m in re.findall(r'"(VerifiedGarbage\.[A-Za-z0-9_.]+)"', lf):
    if not m.startswith('VerifiedGarbage.Spec.'): extra.add(m)
for f in os.listdir(LEAN):
    if f.endswith('.lean'):
        for m in re.findall(r'^import\s+(VerifiedGarbage[A-Za-z0-9_.]*)', open(LEAN + f).read(), re.M):
            extra.add(m)
rootmod = lambda m: m.startswith(ROOTPRE) or m in extra
# import graph
imp_re = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)
imports, src = {}, {}
for top in ('VerifiedGarbage', 'VerifiedGarbageTest'):
    for dp, _, fs in os.walk(LEAN + top):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(dp, f); m = os.path.relpath(p, LEAN)[:-5].replace('/', '.')
                if m in GONE: continue
                src[m] = open(p).read()
                imports[m] = [x for x in imp_re.findall(src[m]) if x.startswith('VerifiedGarbage') and x not in GONE]
reach, st = set(), [m for m in imports if rootmod(m)]
while st:
    m = st.pop()
    if m in reach: continue
    reach.add(m); st.extend(imports.get(m, ()))
# declarations with attributes
kw = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+|public\s+|meta\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|example)\b')
NOUSE = {'irreducible', 'reducible', 'semireducible', 'inline', 'expose', 'specialize', 'noinline'}
attributed = set()
lines_of = {}
for d, m in decl_mod.items():
    if m not in src: continue
    if m not in lines_of: lines_of[m] = src[m].split('\n')
    L = lines_of[m]; a, b = ranges[d][0], ranges[d][2]
    head = []
    for i in range(a, min(b + 1, len(L))):
        head.append(L[i])
        mm = kw.match(L[i])
        if mm: break
    h = '\n'.join(head)
    inst = re.search(r'^\s*(?:@\[[^\]]*\]\s*)*(?:\w+\s+)*instance\b', h, re.M)
    attrs = [a.strip() for x in re.findall(r'@\[([^\]]*)\]', h) for a in x.split(',')]
    # attributes that only set how a definition unfolds or compiles use nothing
    if inst or any(a not in NOUSE for a in attrs):
        attributed.add(d)
# `attribute [...] x` commands are module-level references (modcmd), live once
# their module is used.
implicit = {d for d in attributed if decl_mod[d] in reach}
L, usedmods = set(), set()
st = [d for d, m in decl_mod.items() if rootmod(m)] + sorted(implicit)
st_mods = [m for m in modcmd if m in reach]
while st or st_mods:
    while st_mods:
        m = st_mods.pop()
        if m in usedmods: continue
        usedmods.add(m)
        for c in modcmd.get(m, ()):
            n = norm(c)
            if n: st.append(n)
            elif cmod.get(c, '').startswith('VerifiedGarbage'): st_mods.append(cmod[c])
    while st:
        x = st.pop()
        if x in L: continue
        L.add(x)
        st_mods.append(decl_mod[x])
        for c in E[x]:
            n = norm(c)
            if n: st.append(n)
            elif cmod.get(c, '').startswith('VerifiedGarbage'): st_mods.append(cmod[c])
dead = {d for d in nodes if d not in L}
pickle.dump((L, usedmods, dead, reach, attributed, imports), open(sys.argv[2], 'wb'))
print('live', len(L), 'dead', len(dead), 'attributed', len(attributed), 'implicit', len(implicit), 'reach', len(reach), 'mods', len(imports))
