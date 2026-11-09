# Prototype (unverified) FIOS Montgomery kernel for ppc64le, rows blocked 4 words at a time with 4 carry chains
# (lo a*b, hi a*b, lo u*m, hi u*m) each saved in a GPR between blocks. bench/ branch only.
# Interface as MontMul.kernel: r3 = y, r4 = 2w, r5 o, r6 a, r7 b, r8 T, r9 tmp, r10 m, r14 kept; returns r11 = 2w, r12 = y.
import sys
L=[]
def e(*s): L.extend(s)
X=["%r18","%r19","%r20","%r22"]; Y=["%r23","%r24","%r25","%r26"]; S=["%r27","%r28","%r29","%r30"]; P=["%r31","%r21","%r0","%r11"]
cA,cB,cC,cD="%r3","%r4","%r5","%r9"; hA,hC="%r14","%r15"; Z="%r12"; A="%r17"; U="%r16"; TP,BP,MP,CNT="%r6","%r7","%r10","%r8"
saves=[("%r14",-8),("%r21",-16),("%r23",-24),("%r24",-32),("%r25",-40),("%r26",-48),("%r27",-56),("%r28",-64),
       ("%r29",-72),("%r30",-80),("%r31",-88),("%r5",-96),("%r9",-104),("%r6",-136),("%r7",-144),("%r8",-152),("%r10",-160)]
MPR,W,RND,REM,QQ=-112,-120,-128,-168,-176
def chain(c, v, k):
    e(f"addic {c}, {c}, -1"); e(*[f"adde {S[i]}, {S[i]}, {v[i]}" for i in range(k)]); e(f"addze {c}, {Z}")
def block(k):
    e(*[f"ld {X[i]}, {8*i}({BP})" for i in range(k)], *[f"ld {Y[i]}, {8*i}({MP})" for i in range(k)],
      *[f"ld {S[i]}, {8*i}({TP})" for i in range(k)])
    for i in range(k): e(f"mulld {P[i]}, {A}, {X[i]}", f"mulhdu {X[i]}, {A}, {X[i]}")
    chain(cA, P, k); chain(cB, [hA]+X, k); e(f"mr {hA}, {X[k-1]}")
    for i in range(k): e(f"mulld {P[i]}, {U}, {Y[i]}", f"mulhdu {Y[i]}, {U}, {Y[i]}")
    chain(cC, P, k); chain(cD, [hC]+Y, k); e(f"mr {hC}, {Y[k-1]}")
    e(*[f"std {S[i]}, {8*i-8}({TP})" for i in range(k)])
    e(f"addi {TP}, {TP}, {8*k}", f"addi {BP}, {BP}, {8*k}", f"addi {MP}, {MP}, {8*k}")
for r,o in saves: e(f"std {r}, {o}(%r1)")
# m' = y (2 + m0 y) mod 2^64 (as the verified kernel)
e("mr %r12, %r3", "ld %r0, 0(%r10)", "mulld %r3, %r0, %r12", "addi %r3, %r3, 2", "mulld %r3, %r3, %r12", f"std %r3, {MPR}(%r1)")
e("srdi %r4, %r4, 1", f"std %r4, {W}(%r1)", f"std %r4, {RND}(%r1)", "addi %r0, %r4, -1", "andi. %r3, %r0, 3", f"std %r3, {REM}(%r1)",
  "srdi %r0, %r0, 2", f"std %r0, {QQ}(%r1)")
e("mr %r29, %r8", "addi %r30, %r4, 1", "li %r0, 0", "1:", "std %r0, 0(%r29)", "addi %r29, %r29, 8", "addi %r30, %r30, -1",
  "cmpldi %cr0, %r30, 0", "bne %cr0, 1b")
e(f"li {Z}, 0")
e("2:")  # round
e(f"ld %r3, -136(%r1)", f"ld {A}, 0(%r3)", "addi %r3, %r3, 8", "std %r3, -136(%r1)")
e(f"ld {TP}, -152(%r1)", f"ld {BP}, -144(%r1)", f"ld {MP}, -160(%r1)", f"ld {U}, {MPR}(%r1)")
e(f"ld {S[0]}, 0({TP})", f"ld {X[0]}, 0({BP})", f"ld {Y[0]}, 0({MP})",
  f"mulld {P[0]}, {A}, {X[0]}", f"mulhdu {hA}, {A}, {X[0]}", f"addc {S[0]}, {S[0]}, {P[0]}", f"addze {cA}, {Z}",
  f"mulld {U}, {U}, {S[0]}", f"mulld {P[0]}, {U}, {Y[0]}", f"mulhdu {hC}, {U}, {Y[0]}", f"addc {S[0]}, {S[0]}, {P[0]}",
  f"addze {cC}, {Z}", f"li {cB}, 0", f"li {cD}, 0", f"addi {TP}, {TP}, 8", f"addi {BP}, {BP}, 8", f"addi {MP}, {MP}, 8")
e(f"ld {CNT}, {REM}(%r1)", f"cmpldi %cr0, {CNT}, 1", "beq %cr0, 31f", f"cmpldi %cr0, {CNT}, 2", "beq %cr0, 32f",
  f"cmpldi %cr0, {CNT}, 3", "beq %cr0, 33f", "b 30f")
for k in (1,2,3):
    e(f"3{k}:"); block(k); e("b 30f")
e("30:", f"ld {CNT}, {QQ}(%r1)", f"cmpldi %cr0, {CNT}, 0", "beq %cr0, 35f", "34:")
block(4)
e(f"addi {CNT}, {CNT}, -1", f"cmpldi %cr0, {CNT}, 0", "bne %cr0, 34b", "35:")
# top: T_w + carries + high words -> T_{w-1}, carry out -> T_w
x,y=S[0],S[1]
e(f"ld {x}, 0({TP})", f"addic {cA}, {cA}, -1", f"adde {x}, {x}, {Z}", f"addze {y}, {Z}",
  f"addic {cB}, {cB}, -1", f"adde {x}, {x}, {hA}", f"addze {y}, {y}",
  f"addic {cC}, {cC}, -1", f"adde {x}, {x}, {Z}", f"addze {y}, {y}",
  f"addic {cD}, {cD}, -1", f"adde {x}, {x}, {hC}", f"addze {y}, {y}", f"std {x}, -8({TP})", f"std {y}, 0({TP})")
e(f"ld %r3, {RND}(%r1)", "addi %r3, %r3, -1", f"std %r3, {RND}(%r1)", "cmpldi %cr0, %r3, 0", "bne %cr0, 2b")
# final subtraction and selection
e("ld %r5, -96(%r1)", "ld %r9, -104(%r1)", "ld %r8, -152(%r1)", "ld %r10, -160(%r1)", f"ld %r4, {W}(%r1)", "sldi %r11, %r4, 1",
  f"ld %r3, {MPR}(%r1)", "sldi %r12, %r3, 32", "srdi %r12, %r12, 32")
e("addi %r14, %r8, 0", "addi %r15, %r9, 0", "addi %r16, %r10, 0", "mr %r17, %r4", "subfc %r0, %r0, %r0", "5:",
  "ld %r0, 0(%r14)", "ld %r3, 0(%r16)", "subfe %r0, %r3, %r0", "std %r0, 0(%r15)", "addi %r14, %r14, 8",
  "addi %r15, %r15, 8", "addi %r16, %r16, 8", "addi %r17, %r17, -1", "cmpldi %cr0, %r17, 0", "bne %cr0, 5b",
  "ld %r0, 0(%r14)", "li %r3, 0", "subfe %r0, %r3, %r0", "subfe %r20, %r20, %r20", "addi %r14, %r8, 0",
  "addi %r15, %r9, 0", "addi %r16, %r5, 0", "mr %r17, %r4", "6:",
  "ld %r0, 0(%r15)", "ld %r3, 0(%r14)", "xor %r3, %r3, %r0", "and %r3, %r3, %r20", "xor %r3, %r3, %r0",
  "std %r3, 0(%r16)", "addi %r14, %r14, 8", "addi %r15, %r15, 8", "addi %r16, %r16, 8", "addi %r17, %r17, -1",
  "cmpldi %cr0, %r17, 0", "bne %cr0, 6b")
for r,o in saves:
    if r not in ("%r5","%r9","%r6","%r7","%r8","%r10") or r=="%r10": e(f"ld {r}, {o}(%r1)")
e("blr")
body="\n".join(L)
if sys.argv[1:]==["asm"]:
    print(".text\n.globl kern\n.type kern,@function\nkern:\n"+body)
else:
    print('''// PROTOTYPE, hand-written and unverified: for a bench/ branch's Benchmarks runs only, never merged.
#![allow(dead_code)]
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_rsa_mont_kernel() {
    core::arch::naked_asm!(
        r#"''' + body + '''"#
    )
}''')
