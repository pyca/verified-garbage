import sys
G=[tuple(map(int,l.split())) for l in open('../n/notes/results/'+sys.argv[1]) if l.strip()]
I,O,fn=sys.argv[2],sys.argv[3],sys.argv[4]
with open(fn,'w') as f:
    for j in range(8): f.write(f'i {j} {I[j]}\n')
    for j in range(8): f.write(f'o {200+j} {O[j]}\n')
    for o,d,a,b in G: f.write(f'g {"XA"[o]} {d} {a} {b}\n')
