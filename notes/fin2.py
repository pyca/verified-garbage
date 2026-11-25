import sys
S=sys.argv[1]
src=open(S+'/proto/lim.py').read(); pre=src.split("ch='A D")[0].replace("sys.argv=['x',sys.argv[1]]","").replace("sys.argv[1]",repr(S))
exec(pre)
for n in ('base','adx'):
    for o in 'A C s'.split():
        parts[f'{n} {o}t']='\n'.join(l for l in parts[f'{n} {o}'].split('\n') if not re.match(r'adc r(9|10|11), 0',l))
    # E with AA (its minuend) still in r8-r11
    parts[f'{n} Er']='\n'.join(l for l in parts[f'{n} E'].split('\n') if not re.match(r'mov r\d+, QWORD',l))
    # s with Q still in registers
    t=parts[f'{n} s'].split('\n'); parts[f'{n} sr']='\n'.join(l.replace('+416','+448') if 0 else l for l in t if not re.match(r'mov r\d+, QWORD',l))
def sub(o,**k): return ' '.join(k.get(x,x) for x in o.split())
b='D A C B UV P BB AA E Q w d x2 s dd z2 x3 z3'
O=[b,sub(b,A='At',C='Ct',s='st'),sub(b,E='Er'),sub(b,A='At',C='Ct',s='st',E='Er'),'D A C B UV P BB AA E Q s w d x2 dd z2 x3 z3','D A C B UV P BB AA E Q sr w d x2 dd z2 x3 z3', 'D At Ct B UV P BB AA Er Q w d x2 st dd z2 x3 z3']
t={}
for z in range(5):
    r=list(map(float,build([(n,o.split()) for n in ('base','adx') for o in O])))
    for i,o in enumerate(O): t.setdefault(i,[]).append((r[i]/r[0],r[i+len(O)]/r[len(O)]))
for i,o in enumerate(O): print([('%.3f/%.3f'%x) for x in t[i]],o)
