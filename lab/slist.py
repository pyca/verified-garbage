"""SSA list scheduling of a straight-line body: chains of flag users stay whole."""
import re, heapq, random
SET = ('adds','adcs','subs','sbcs','tst'); READ = ('adcs','adc','sbcs','sbc','csel')
LAT = {'mul': 2, 'umulh': 3, 'ldp': 4, 'ldr': 4, 'ldrb': 4}
def parse(l):
    op, _, rest = l.partition(' ')
    m = re.match(r'(.*?),\s*\[(\w+)(?:,\s*#(\d+))?\]$', rest)
    if m:
        rs = [r.strip() for r in m[1].split(',')]; base, off = m[2], int(m[3] or 0)
        if op in ('ldr','ldp'): return op, rs, [base], ('L', off, 8*len(rs)) if base == 'x0' else ('L', None, 0), rest
        if op == 'ldrb': return op, rs, [base], None, rest
        return op, [], rs + [base], ('S', off, 8*len(rs)), rest
    o = [x.strip() for x in rest.split(',')]
    if op == 'tst': return op, [], o, None, rest
    d = [o[0]]; u = [x for x in o[1:] if re.match(r'[xw]\d+$', x)]
    if op == 'movk': u = [o[0]] + u
    return op, d, u, None, rest
N = lambda r: int(r[1:])
def units(body):
    """Maximal chains: from a setter to its last reader before the next fresh setter."""
    U, cur = [], []
    for i, l in enumerate(body):
        op = l.split()[0]
        if op in READ and cur: cur.append(i)
        elif op in SET:
            if cur: U.append(cur)
            cur = [i]
        else: U.append(('x', i))
    if cur: U.append(cur)
    return U
def build(body, fixed):
    P = [parse(l) for l in body]
    # group chains (non-flag instructions between stay single)
    group = {}; gid = 0; cur = None
    for i, p in enumerate(P):
        op = p[0]
        if op in SET and op not in READ: cur = gid; gid += 1; group[i] = cur
        elif op in READ: group[i] = cur
    nodes = {}
    for i in range(len(P)): nodes.setdefault(('g', group[i]) if i in group else ('i', i), []).append(i)
    # SSA
    fl = {}; last = {}; vreg = 0; defs, uses = {}, {}; memw = []; deps = {k: {} for k in nodes}
    owner = {i: k for k, v in nodes.items() for i in v}
    stores, loads = [], []; dv = {}
    for i, (op, d, u, mem, _) in enumerate(P):
        uses[i] = []
        for r in u:
            n = N(r)
            if n in fixed:
                uses[i].append(('f', n))
                if n in fl and owner[fl[n]] != owner[i]: deps[owner[i]][owner[fl[n]]] = 1
                continue
            v = last[n]; uses[i].append(v); a = dv[v]
            if owner[a] != owner[i]: deps[owner[i]][owner[a]] = max(deps[owner[i]].get(owner[a], 0), LAT.get(P[a][0], 1))
        defs[i] = []
        for r in d:
            n = N(r)
            if n in fixed: defs[i].append(('f', n)); fl[n] = i; continue
            last[n] = vreg; dv[vreg] = i; defs[i].append(vreg); vreg += 1
        if mem and mem[1] is not None:
            kind, off, ln = mem
            for (o2, l2, j) in stores:
                if o2 < off + ln and off < o2 + l2 and owner[j] != owner[i]: deps[owner[i]][owner[j]] = max(deps[owner[i]].get(owner[j], 0), 5 if kind == 'L' else 0)
            if kind == 'S':
                for (o2, l2, j) in loads:
                    if o2 < off + ln and off < o2 + l2 and owner[j] != owner[i]: deps[owner[i]].setdefault(owner[j], 0)
                stores.append((off, ln, i))
            else: loads.append((off, ln, i))
    return P, nodes, deps, defs, uses
def schedule(body, fixed, regs, limit, width=5.0, seed=None, wl=1.0, W=10**9):
    P, nodes, deps, defs, uses = build(body, fixed)
    succ = {k: [] for k in nodes}
    for k, d in deps.items():
        for a, l in d.items(): succ[a].append((k, l))
    prio = {}
    import sys; sys.setrecursionlimit(10000)
    def pr(k):
        if k in prio: return prio[k]
        prio[k] = (len(nodes[k]) if k[0] == 'g' else LAT.get(P[nodes[k][0]][0], 1)) + max([pr(s) + 0 for s, l in succ[k]], default=0)
        return prio[k]
    for k in nodes: pr(k)
    rnd = random.Random(seed); jit = {k: rnd.random() * (8 if seed else 0) for k in nodes}
    nuse = {}
    for i in uses:
        for v in uses[i]:
            if not isinstance(v, tuple): nuse[v] = nuse.get(v, 0) + 1
    remaining = {k: len(d) for k, d in deps.items()}; avail = {k: 0.0 for k in nodes if remaining[k] == 0}
    live = set(); t = 0.0; order = []; first = {k: min(v) for k, v in nodes.items()}
    while avail:
        def effect(k):
            """net change in live values; and the peak within"""
            cnt = dict(); cur = 0; peak = 0
            for i in nodes[k]:
                for v in uses[i]:
                    if isinstance(v, tuple): continue
                    cnt[v] = cnt.get(v, 0) + 1
                    if cnt[v] == nuse[v]: cur -= 1
                for v in defs[i]:
                    if not isinstance(v, tuple): cur += 1
                peak = max(peak, cur)
            return cur, peak
        lo = min(first[k] for k in avail)
        c = [(k,) + effect(k) for k in avail if first[k] <= lo + W]
        ok = [x for x in c if len(live) + x[2] <= limit]
        ready = [x for x in ok if avail[x[0]] <= t]
        if ready: k = max(ready, key=lambda x: (prio[x[0]] - wl * 10 * max(0, x[1]) * (len(live) > limit - 6) - 0.02 * first[x[0]] + jit[x[0]]))[0]
        elif ok:
            # what frees registers or comes first in time
            k = min(ok, key=lambda x: (avail[x[0]], -prio[x[0]]))[0]; t = max(t, avail[k])
        else: k = min(c, key=lambda x: (x[2], first[x[0]]))[0]
        del avail[k]; order.append(k)
        for i in nodes[k]:
            for v in uses[i]:
                if isinstance(v, tuple): continue
                nuse[v] -= 1
                if nuse[v] == 0: live.discard(v)
            for v in defs[i]:
                if not isinstance(v, tuple) and nuse.get(v, 0) > 0: live.add(v)
        for s, l in succ[k]:
            remaining[s] -= 1
            avail_t = max(getattr(schedule, '_a', {}).get(s, 0), t + l + (len(nodes[k]) - 1))
            schedule._a = getattr(schedule, '_a', {}); schedule._a[s] = avail_t
            if remaining[s] == 0: avail[s] = avail_t
        t += len(nodes[k]) / width
    schedule._a = {}
    # allocation
    seq = [i for k in order for i in nodes[k]]
    pos = {i: p for p, i in enumerate(seq)}; end = {}
    for i in seq:
        for v in uses[i]:
            if not isinstance(v, tuple): end[v] = max(end.get(v, 0), pos[i])
    free = list(regs); amap = {}; out = []; mx = 0
    for i in seq:
        op, d, u, mem, rest = P[i]
        ul = [f'x{v[1]}' if isinstance(v, tuple) else amap[v] for v in uses[i]]
        for v in set(x for x in uses[i] if not isinstance(x, tuple)):
            if end[v] == pos[i]: free.insert(0, amap[v]) if False else free.append(amap[v])
        if op == 'movk': # tied
            pass
        dl = []
        for v in defs[i]:
            if isinstance(v, tuple): dl.append(f'x{v[1]}'); continue
            if op == 'movk':
                r = ul[0]; free.remove(r)
            else:
                if not free: return None
                r = free.pop(0)
            amap[v] = r; dl.append(r)
        for v in defs[i]:
            if not isinstance(v, tuple) and v not in end: free.append(amap[v])
        mx = max(mx, len(regs) - len(free))
        # rewrite
        if mem or op == 'ldrb':
            tail = rest[rest.index('['):]
            regs_ = dl if op.startswith('ld') else ul[:-1]
            if op == 'ldrb': tail = tail.replace(re.search(r'\[(x\d+)', tail)[1], ul[0], 1); regs_ = ['w' + r[1:] for r in regs_]
            out.append(f'{op} {", ".join(regs_)}, {tail}')
        else:
            o = [x.strip() for x in rest.split(',')]; it = iter(ul); new = []
            for q, x in enumerate(o):
                if re.match(r'[xw]\d+$', x):
                    if op != 'tst' and q == 0: r = dl[0]; (next(it) if op == 'movk' else None)
                    else: r = next(it)
                    new.append(x[0] + r[1:])
                else: new.append(x)
            out.append(f'{op} {", ".join(new)}')
    return out, mx
