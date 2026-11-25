# Working for the x86-64 X25519 ladder (before any code)

Seen beforehand: what remains of the interface (Field, addCmov/subCmov, the IFMA ladder, the
slot environment, Main, Finish, Setup, Bits). Among the remains: `opMux`'s signature (a choice
of two slots by zf), `store4Z_ok` ("also keeps the flags"), and LPre's fields, which include
that bits 0, 1, 2 are zero. They hint at how the old code was arranged; the derivations below
stand alone.

## The step (RFC 7748 section 5)
A=x2+z2 B=x2-z2 C=x3+z3 D=x3-z3 (after cswap); P=D*A Q=C*B; AA=A^2 BB=B^2 E=AA-BB;
x3=(P+Q)^2 z3=x1*(P-Q)^2 x2=AA*BB z2=E*(AA+a24*E).
4 squarings, 5 multiplications, 1 a24add, 7 sums/differences.
Levels: {A B C D} {P Q AA BB} {s d E x2} {x3 dd w} {z3 z2}.
Longest chain: D,A -> P -> d -> dd -> z3: 2 mul + 1 sqr + 2 sums.

## Selecting the point
Swapping (x2,z2) with (x3,z3) swaps (A,B) with (C,D). Then P=D*A becomes B*C=Q and Q=C*B
becomes A*D=P: P+Q is unchanged, P-Q changes sign and is only squared. So x3 and z3 need no
selection: compute A,B,C,D from the unswapped state, and select only the operands of the
doubling, U = swap ? C : A, V = swap ? D : B. 8 words (8 load + 8 cmov-load + 8 stores = 24
instructions, no masks) against 16 word pairs (4 loads/stores + 5 logic each) for cswap.
(I also recognise this as a known trick; it is derived above from the formulas.)
swap = k_t xor k_(t+1): two bytes of BITS, xor, ZF for cmov. No stored swap. At t=254, k_255
must read as 0, but BITS+255 holds bit 7 of byte 31 of the scalar unmasked: clear it first.

## Three cleared low bits
k_2=k_1=k_0=0. At t=2 the doubled point is selected by k_3; then always (x2,z2), and x3,z3 of
these three are never used. So: ladder t=254..3 (252 steps); select (x2,z2) by k_3; three
doublings of 2S+2M+1 a24+3 sums. Saves 3*(2S+3M+4 sums) of about 255*(4S+5M..): 0.6%.
The final swap is k_0=0, so SWAP, 0 from setup, is right unwritten.

## Bounds
addCmov needs one operand <= 2p, subCmov the subtrahend <= 2p; mul and sqr give <= 2p.
Invariant: z2,z3 <= 2p. A,B: z2; C,D: z3; s,d: P,Q; E: BB. x1 and the sums are only factors.
Doublings: the selected z is one of two <= 2p.

## Order and slots (order.py, order2.py)
Macro model (uops, latency, multiplier cycles by op; widths 4/6, windows 224/256/512, baseline and
ADX counts), hill-climbed from the RFC order over topological orders. Cycles per step:
  RFC order          base 409/352/306  adx 279/260/260
  best free          base 404/261/240  adx 279/211/208
  best, U V adjacent base 407/261/240  adx 279/211/208
Selecting U and V together costs nothing (one flag). Chosen, from the latter:
  A B D C (U V) P AA BB Q E s x2 d w dd z2 x3 z3
i.e. neighbours are independent; the two halves (doubling, addition) interleave.
Slots (7 live at once): x2..z3 = 3..6; A 7 B 8 C 9 D 10 U 11 V 12; P in 10, Q in 9, AA in 11,
BB in 12, E in 8, s in 7, d and dd in 9, w in 11. Only slots 3-12 used.

## After a first version in Lean (unproven), measured locally (Sapphire Rapids, tsc/op, one process)
Order matters as the model says: RFC order 15% slower than the chosen one (base 51227 vs 44661,
adx 43832 vs 38292); against main as a black box the first version is 1.0% (base) and 1.8% (adx)
slower. A loop whose operations write slots nothing reads (no dependencies between operations)
is 4.5% (base), 9% (adx) faster: so there is latency left to hide, not only instructions.
Ideas, in the order to try:
1. climb over orders on the hardware rather than in the model (ord.py), one order for both fields;
2. one block for A, B and the selection (the sums are still in registers when selected): saves
   8 loads and store-to-load latency. First try: no gain alone (base +0.5%, adx -0.7% by order);
3. the first iteration is known (k_254 = 1, so swap = 1, x2 = 1, z2 = 0): 0.2%;
4. shorter folds: products are below 2^255 + 2^12, so a sum's carry can be folded into its low
   word alone (3 instructions of 23), if mul's bound is stated so.

Results of 1-4: climbing on the hardware (climb.py) gives
  D A C B UV P BB AA E Q w d x2 s dd z2 x3 z3
2.0-2.6% (base) and 2-5% (adx) faster than the model's (fin.py): the doubling, the longer of the
two chains through latency-heavy pieces (sqr, sub, a24add, mul), starts early. One block for A, B, U, V:
slower on base, no better on adx. Short folds (fin2.py): at most 0.7% on base, 0.2% on adx.
Reusing registers for E or s: nothing. Not worth their proofs; left out. 3 not tried.
Slots for this order: P in D, BB in DV, AA in DU, E in A, Q in C, w in B, d and dd in Z3 (z3's old
value is dead after D and C), s in D. Slots 2-12.
