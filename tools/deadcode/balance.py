import os, sys,re
for p in sys.argv[1:]:
    try: L=open(p).read().split('\n')
    except FileNotFoundError: continue
    st=[]; bad=None; inc=0
    for i,l in enumerate(L):
        if l.startswith('/-'): inc+= 0
        m=re.match(r'^(namespace|section|noncomputable section|public section|@\[expose\] public section|public meta section)\b ?(\S*)',l)
        if m and not l.startswith('section') or (m and l.startswith('section')):
            if m: st.append(m.group(2)); continue
        m=re.match(r'^end\b ?(\S*)\s*$',l)
        if m:
            if not st: bad=(i+1,'unmatched end'); break
            t=st.pop()
            if m.group(1) and t and m.group(1)!=t: bad=(i+1,f'end {m.group(1)} closes {t}'); break
    if bad: print(p,bad)
