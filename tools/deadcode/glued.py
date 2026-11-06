import os, sys,re
for p in sys.argv[1:]:
    try: L=open(p).read().split('\n')
    except FileNotFoundError: continue
    n=0
    for i in range(1,len(L)):
        if re.match(r'^(/--|/-!|theorem |def |abbrev |structure |private |@\[|noncomputable |instance |end |namespace |section)',L[i]) and L[i-1].strip() and not re.match(r'^(/--|@\[|.*-/$|namespace |section|open |variable|end |@\[expose\]|public section|noncomputable section|meta )',L[i-1]) and not L[i-1].startswith('--'):
            n+=1
    print(n, p.split('/lean/',1)[-1] if '/lean/' in p else p)
