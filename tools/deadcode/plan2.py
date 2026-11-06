# Removal set: dead declarations of the algorithms in $SCOPE (comma-separated directory names under Proof/ and Impl/, e.g. Weierstrass,Ecdh) whose every referrer is removed too.
# Extends plan.py: a module of the scope with no declarations of its own
# (a `materialize_code` Lit module, whose literal is no graph node) goes
# when nothing live is among what its commands reference and every
# reference it has in scope is removed.
# usage: plan2.py graph.pkl live.pkl [prev_plan.pkl] -> plan.pkl (C, gone), keeps.txt
# With a previous plan (whose deleted modules live4 left out), its deletions stay.
import pickle, sys, re, os
from collections import defaultdict, Counter
S = os.environ.get('WORK', '.') + '/'
decl_mod, edges, modcmd, cmod, ranges = pickle.load(open(S + sys.argv[1], 'rb'))
L, U, D, R, A, I = pickle.load(open(S + sys.argv[2], 'rb'))
nodes = set(decl_mod)
def norm(c):
    while c not in nodes and '.' in c: c = c.rsplit('.', 1)[0]
    return c if c in nodes else None
ALGS = [a for a in os.environ['SCOPE'].split(',') if a]
scope = lambda m: m.startswith(tuple(f'VerifiedGarbage.{k}.{a}.' for a in ALGS for k in ('Proof', 'Impl')))
own = lambda m: any(a in m for a in ALGS)  # an in-scope algorithm's own registration file, by name
REV = defaultdict(set)
for d, cs in edges.items():
    p = d if d in nodes else norm(d)
    for c in cs:
        n = norm(c)
        if n and n != p: REV[n].add(p if p else ('?', d))
for m, cs in modcmd.items():
    for c in cs:
        n = norm(c)
        if n: REV[n].add(('mod', m))
allm = Counter(decl_mod.values())
# Modules of other algorithms' registrations (Artifacts/Generic/Variants files
# outside $SCOPE) import are never deleted: their dead declarations go only when
# others stay, and a module with none live is kept whole.
reg = lambda m: m.startswith(('VerifiedGarbage.Artifacts.', 'VerifiedGarbage.Generic.', 'VerifiedGarbage.Variants.'))
protected = set()
for m, ims in I.items():
    if reg(m) and not own(m):
        protected |= {x for x in ims if scope(x)}
PREV = pickle.load(open(S + sys.argv[3], 'rb'))[1] if len(sys.argv) > 3 else set()
# Modules that define syntax (tactics, macros, notation): what uses it leaves no
# reference, so they are never deleted either (their declarations may go).
SYN = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:scoped |local )?(?:tactic_template|macro_rules|macro|syntax|elab_rules|elab|notation|infixl?|infixr|prefix|postfix|declare_syntax_cat)\b', re.M)
SRCDIR = os.environ.get('SRC', os.environ.get('REPO', os.getcwd())) + '/lean/'
syntaxmods = {m for m in I if scope(m) and SYN.search(open(SRCDIR + m.replace('.', '/') + '.lean').read())}
C = {d for d in D if scope(decl_mod[d])} | {d for d, m in decl_mod.items() if m in PREV}
declless = {m for m in set(I) | PREV if scope(m) and allm[m] == 0 and m not in protected and m not in syntaxmods}
def refs(m): return {n for n in (norm(c) for c in modcmd.get(m, ())) if n}
log = open(S + 'keeps.txt', 'w')
while True:
    cnt = Counter(decl_mod[d] for d in C)
    full = {m for m in cnt if cnt[m] == allm[m]}
    for m in full & protected:
        print('keep whole (imported by', sorted(x for x, ims in I.items() if reg(x) and not own(x) and m in ims)[:2], ')', m, file=log)
        C -= {d for d in C if decl_mod[d] == m}
    gone = full - protected - syntaxmods
    gone |= {m for m in declless if all(n in C or (n not in L and not scope(decl_mod[n])) for n in refs(m))
             and not any(n in L for n in refs(m))}
    changed = False
    for d in list(C):
        ext = [r for r in REV[d] if not ((isinstance(r, tuple) and r[0] == 'mod' and r[1] in gone)
                                         or (isinstance(r, str) and r in C))
               and not (isinstance(r, tuple) and r[0] == 'mod' and r[1] == decl_mod[d])]
        if ext:
            C.discard(d); changed = True
            print('keep', d, 'used by', ext[:3], file=log)
    if not changed: break
cnt = Counter(decl_mod[d] for d in C)
print('remove', len(C), 'decls in', len(cnt), 'modules;', len(gone), 'modules deleted (',
      len(gone & declless), 'without declarations );', len(protected), 'protected modules')
pickle.dump((C, gone), open(S + 'plan.pkl', 'wb'))
