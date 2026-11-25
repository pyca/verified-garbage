import random
def rows(l): return [sum(1<<b for b in r) for r in l]
M=rows([[0, 1, 3], [2, 3, 6, 7], [4, 5, 7], [1, 2, 3, 5], [1, 2, 4], [3, 4], [2, 3, 4, 5], [4, 5, 6]])
P0=rows([[2, 4, 5, 6], [2, 4, 6, 7], [0, 1, 4, 6], [0, 2, 4, 5, 6, 7], [0, 2, 3, 4, 6],[0, 1, 3, 5, 6], [0, 4, 5, 6], [1, 3, 6, 7]])
P1=rows([[1, 3], [1, 4, 5, 6, 7], [0, 2, 3, 4, 6], [0, 1, 3, 4, 5, 6], [3, 6, 7], [3, 4, 5, 6],[1, 2, 3, 6], [3]])
def rank(A):
    A=list(A);r=0
    for b in range(8):
        p=next((i for i in range(r,8) if A[i]>>b&1),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]
        for i in range(8):
            if i!=r and A[i]>>b&1:A[i]^=A[r]
        r+=1
    return r
print(rank(P0),rank(P1),rank([a^b for a,b in zip(P0,P1)]))
def search(A,n=4000):
    best=None
    for t in range(n):
        # reduce A by row ops (reverse) and col ops to permutation
        R=list(A);rowops=[];colops=[]
        cost=lambda R:sum(bin(x).count('1') for x in R)
        while cost(R)>8:
            c=cost(R);c2=sum((bin(x).count('1')) for x in inv(R)) if False else 0
            cand=[]
            for i in range(8):
                for j in range(8):
                    if i==j: continue
                    d=bin(R[i]^R[j]).count('1')-bin(R[i]).count('1')
                    cand.append((d,random.random(),'r',i,j))
                    # col i ^= col j
                    d=sum((1 if not(x>>i&1) else -1) for x in R if x>>j&1)
                    cand.append((d,random.random(),'c',i,j))
            cand.sort()
            d,_,k,i,j=cand[0] if random.random()<.9 else cand[random.randrange(4)]
            if d>=0 and random.random()<.0: break
            if k=='r': R[i]^=R[j];rowops.append((i,j))
            else:
                R=[x^((x>>j&1)<<i) for x in R];colops.append((i,j))
            if len(rowops)+len(colops)>30: break
        if cost(R)!=8 or any(bin(x).count('1')!=1 for x in R) : continue
        ops=len(rowops)+len(colops)
        if best is None or ops<best[0]:
            # A = rowops^-1 ... : R = Rk..R1 A C1..Cm ; A = R1..Rk R Cm^-1..C1^-1 (reverse)
            # col op: col i ^= col j equals right mult by E where E: x_i.. : (A E): A[:,i]+=A[:,j] -> E = I + e_j e_i^T ; as action on vector: x_j ^= x_i
            # A x = rows(R (Em^-1 ... E1^-1 x))... A = R' .. ; A C1..Cm = P => A = P Cm..C1 ; so apply C1 first? (Cm^-1=Cm) x -> C1 first: no A=P Cm ... C1, C1 first
            # wait A C1 ... Cm = P => A = P Cm ... C1
            seq=[]
            perm=[R[i].bit_length()-1 for i in range(8)] # row i = input perm[i]
            for (i,j) in colops: seq.append((j,i)) # x_j ^= x_i
            # registers hold x; after col ops, out row i = reg perm[i]; then row ops reversed
            for (i,j) in reversed(rowops): seq.append((perm[i],perm[j]))
            # check
            X=[1<<k for k in range(8)]
            for d,s in seq: X[d]^=X[s]
            assert [X[perm[i]] for i in range(8)]==list(A)
            best=(ops,seq,perm)
    return best
random.seed(1)
for nm,A in (('M',M),('P0',P0),('P1',P1),('D',[a^b for a,b in zip(P0,P1)])):
    if rank(A)==8: print(nm,search(A))
