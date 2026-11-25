import sys
S=sys.argv[1]
src=open(S+'/proto/lim.py').read(); pre=src.split("ch='A D")[0].replace("sys.argv=['x',sys.argv[1]]","").replace("sys.argv[1]",repr(S))
exec(pre)
O=[l.strip() for l in open(sys.argv[2]) if l.strip()]
t={}
for z in range(4):
    r=list(map(float,build([(n,o.split()) for n in ('base','adx') for o in O])))
    for i,o in enumerate(O): t.setdefault(i,[]).append((r[i]/r[0],r[i+len(O)]/r[len(O)]))
for i,o in enumerate(O): print('base %.4f adx %.4f'%(min(a for a,_ in t[i]),min(b for _,b in t[i])),[('%.3f/%.3f'%x) for x in t[i]],o)
