import sys
P=2**255-19
def x25519(k,u):
    k=int.from_bytes(k,'little'); k&=~7; k&=(1<<255)-1; k|=1<<254
    u=int.from_bytes(u,'little')&((1<<255)-1)
    x1=u;x2=1;z2=0;x3=u;z3=1;sw=0
    for t in range(254,-1,-1):
        b=(k>>t)&1; sw^=b
        if sw: x2,x3=x3,x2; z2,z3=z3,z2
        sw=b
        A=(x2+z2)%P;AA=A*A%P;B=(x2-z2)%P;BB=B*B%P;E=(AA-BB)%P;C=(x3+z3)%P;D=(x3-z3)%P
        DA=D*A%P;CB=C*B%P;x3=(DA+CB)**2%P;z3=x1*(DA-CB)**2%P;x2=AA*BB%P;z2=E*(AA+121665*E)%P
    if sw: x2,x3=x3,x2; z2,z3=z3,z2
    return (x2*pow(z2,P-2,P)%P).to_bytes(32,'little')
bad=0;n=0
for l in sys.stdin:
    s,p,o=[bytes.fromhex(x) for x in l.split()]; n+=1
    if x25519(s,p)!=o: bad+=1; print("MISMATCH",l.strip())
print(n,"checked,",bad,"bad")
