# existing-style saturated: row operand scanning, N2 mca
import sys
acc=[f"x{i}" for i in [8,9,10,11,12,13,14,15,21,22,23]]
b=["x4","x5","x16","x17","x6","x24","x25","x26","x27"]
def mul_rows(full):
    o=[]
    T=acc
    for i in range(9):
        w=lambda j:T[(i+j)%11]
        o.append(f"ldr x1,[x28,#{8*i}]")
        o.append(f"mul x2,x1,{b[0]}"); o.append(f"adds {w(0)},{w(0)},x2")
        for j in range(1,9):
            o.append(f"mul x2,x1,{b[j]}"); o.append(f"adcs {w(j)},{w(j)},x2")
        o.append(f"adcs {w(9)},{w(9)},x7")
        o.append(f"umulh x2,x1,{b[0]}"); o.append(f"adds {w(1)},{w(1)},x2")
        for j in range(1,9):
            o.append(f"umulh x2,x1,{b[j]}"); o.append(f"adcs {w(j+1)},{w(j+1)},x2")
        # friendly reduction
        o.append(f"lsl x2,{w(0)},#9");o.append(f"adds {w(8)},{w(8)},x2")
        o.append(f"lsr x2,{w(0)},#55");o.append(f"adcs {w(9)},{w(9)},x2");o.append(f"adc {w(10)},x7,x7")
        o.append(f"mov {w(0)},#0")
    return o
for l in mul_rows(1): print(l)
