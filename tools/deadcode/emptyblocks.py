import os, sys,re
for p in sys.argv[1:]:
    try: s=open(p).read()
    except FileNotFoundError: continue
    for m in re.finditer(r'\n(namespace [^\n]+|section[^\n]*)\n((?:(?:open|variable|/-![^\n]*-/|--)[^\n]*\n|\s*\n)*)end[^\n]*\n',s):
        print(p.split('/lean/')[-1], m.group(1), m.group(2).count('\n'))
