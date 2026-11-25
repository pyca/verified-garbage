# Working for the baseline GHASH (written before the code)

Sources: SP 800-38D, the ISA models in `lean/VerifiedGarbage/TCB/`, and the
repository's own PMULL/PCLMULQDQ reduction, which stays.

## The product

Integer multiplication is carry-less multiplication plus carries. If operand
`a` has bits only at positions = i (mod k), and `b` at = j (mod k), every
partial product lands at positions = i+j (mod k), and column p's count is at
most the number of bits of one class. If that count is below 2^k it occupies
columns p..p+k-1, so reaches no other column of its class: bit p of the
integer product is the count's parity, the carry-less coefficient. XORing
several such products keeps that bit. One mask per residue is therefore
enough, after the XORs.

Bounds (`check.py`): 32-bit words need k=4 (8 < 16); k=3 fails (11 > 7).
64-bit words need k=5 (13 < 32); k=4 fails only when both classes are full
(16 = 2^4); 60 bits with k=4 fits (15 < 16).

## Candidates on a 64-bit machine (`proto.c`)

Karatsuba over the two words of a block, so three 64x64 products.
A: k=5, 25 mul each = 75 (128-bit products).
B: 32-bit words, k=4: 9*16 = 144 low multiplications.
C: B with Karatsuba also over the classes (shift classes to residue 0, XOR
   keeps them spread): 9*9 = 81.
D: B with pmuludq, two at a time. MXCSR sequence and two-lane shuffles.
E: 64-bit words, k=4, Karatsuba over classes, 27 mul; the 8 bits of Y in
   bit position 60..63 of each word are added by masks from a table of
   H*x^i, so that no count reaches 16.
F: SSE2 masks and no multiplication (8 bit masks of H, broadcast bytes of
   Y): about 270 and/xor, but the tables do not fit in 256 bytes of scratch.
G: one bit of Y at a time: 128 steps of mask, 2 and, 2 xor: above 600
   operations.

Measured (gcc -O3 -funroll-loops, Xeon 2.1 GHz, TSC cycles per block):
A 75, B 123, C 105, D 87, E 75. At -O2: A 189, B 212, C 177, D 135, E 91.
The compiler's -O2 loops are not what I would emit; straight-line code is.
A and E tie unrolled. A has one lemma to prove and no table of masks, so
A for x86-64; E is the next step if A is slower than main.

## What was seen

No removed file was opened. Seen: the names and modules of the removed
declarations the rest of the tree uses (a list, from the build cache); the
first 20 lines of some files, which included a few lines of code of
`Impl/Gcm/RISCV64/Prepared.lean` (register saves, the call of a block
routine) and the header of `PrepLaw.lean`; and `Spec/Gcm/Bitsliced.lean`,
trusted and unchanged, which fixes a key layout of nine 32-bit operands in
four classes for RISC-V and names BearSSL. I also recognise integer
multiplication with separated bits, as a published technique; the bounds
above are my own derivation, which the rules ask to keep. The trick of
bit-reversing the operands to get a product's high half, and any code
from a library, is not used.

## The other targets (written before their code; x86-64's is A, done)

Operation counts are per block, without loads of the key's words.

RISC-V (RV64IM; `mul` and `mulhu` are two instructions). A costs 75 of each.
B costs 144 `mul` and no `mulhu`: the 32-bit words' classes have at most 8
bits and the product fits 64 bits. B per 32-bit operand: 4 and, 16 mul,
12 xor, 4 and, 3 or = 39, nine operands: 351, plus the Karatsuba sums. C
saves 63 mul and adds about 25 xor and shifts per operand: more in all. The
key layout of `Spec/Gcm/Bitsliced.lean` (nine 32-bit operands, four classes)
is B's key, and is fixed. B, for `vg_ghash` and for the prepared form.

AArch64. A: 75 `mul` + 75 `umulh`; B: 144 `mul`, masks of 32-bit words are
logical immediates in the ISA but not in the model, so masks stay in
registers (5 or 4 of 28). NEON `umull` does two 32-bit products: D, 72.
`vg_ghash_neon` (byte `pmull`, which stays) is what AES-GCM runs without
PMULL, so this code only serves the forced baseline, SM4 without PMULL and
`store_powers`: A, whose algebra is proven, with masks in registers.

ARM (A32, no 64-bit registers). `umaal` with a zeroed pair is the only
32x32->64 product in the model; `mul` gives 32 bits. B with `umaal`: 144 x
(2 mov, umaal, 2 eor) = 720. With `mul` of 16-bit halves, k=3 (16 bits: at
most 6 per column, < 8): 27 products of 16x16 (Karatsuba three deep), each
9 mul, 6 eor, 3 and, 2 orr: 540, plus three levels of Karatsuba and the
splits (27*3 and) about 250: no better, and more to prove. Adding instead of
XORing (`mla`, k=5: 16 pairs < 32) is 27*(25 mul/mla) = 675. B.

x86 (32-bit, 8 GPRs, SSE2). Scalar `mul` ties up eax and edx: 144 x (2 mov,
mul, 2 xor) = 720, with spills. SSE2 `pmuludq` does two products: D, 72
pmuludq, 72 movdqa, 72 pxor and about 60 and/or, half the work. It needs
the MXCSR sequence around it (the rule in CLAUDE.md), once per call. D.

## AArch64, changed before its code

The model's baseline AdvSIMD has `pmull` of bytes (no FEAT_PMULL), and the
repository already has `vg_ghash_neon` with it, which stays and is what
AES-GCM chooses without PMULL. Per block: 45 `pmull` of 8 products each
against A's 150 integer multiplications plus some 250 other operations. A
separate integer `vg_ghash` can only be slower, and needs no less of the ISA.
So no integer code on AArch64: the baseline variants call `vg_ghash_neon`,
and `store_powers` multiplies with its `mul`, seven times in a row
(`H^(k+1) = H^k * H`), without a stack frame.

## ARM, corrected before its code

The model's `umaal` needs a CPU feature (`Instr.requires`): the baseline
includes Cortex-M3, whose long multiplies take a time that depends on their
operands, so only `mul` and `mla` (32 bits of the product) are usable and B
with `umaal` is out.

`mul` is exact for 16-bit operands. Three classes modulo 3: a class has at
most 6 of the 16 bits, and 6 < 2^3, so a product of two classes is right in
its class; the three products of a class are XORed (not added: 3*6 > 7) and
masked: 9 mul, 6 eor, 3 and, 2 eor per 16x16 product. Four classes would allow
no `mla` either: 16 pairs meet in column 15 and 16 = 2^4. Karatsuba three
times: 27 products a block, 243 `mul`. Registers: 3 masks (one set serves
operands and products: 0x49249249 and its shifts), 3 + 3 classes, accumulator,
temporary, result, pointer: 12 of 14. The key's 27 halves take 108 of the 256
bytes of scratch (81 class words would not fit: 324), so its classes are
masked out again for each product, 81 more `and`.

Reduction by 32-bit words: word i of the product (i = 0..3, ascending) adds
w ^ w>>1 ^ w>>2 ^ w>>7 to word i+4 and w<<31 ^ w<<30 ^ w<<25 to word i+3,
with shifted operands (`eor d, d, w, lsr #k`): 7 instructions a word.

## x86, changed before its code

`GhashImpl` (`Proof/AesGcm/X86/Callee.lean`) asks for `stackUse = 0`, and the
contract gives no room below `esp`: D is out, since `pmuludq` runs only in an
MCDT frame (12 bytes of stack). What is left:

E. Scalar `mul` (32x32->64, not on the MCDT list), B's 144: `mov eax,[key
   class]; mov r,[y class]; mul r; xor; xor`, 5 instructions each, 720; 36
   class sums with 2 zeroings, 2 masks, and their additions, about 220; the
   rest (Karatsuba's sums, the reduction, the y classes) in SSE2 by 64-bit
   lanes (`psllq`, `psrlq`, `pxor`), about 120. The y classes of a word come at
   once from a splat and a `pand` with the four masks. About 1050.
F. No multiplication: 27 products of 16x16 bits (Karatsuba three deep) in 7
   vectors of four 32-bit lanes, a bit at a time: `movdqa m,y; psraw m,15; pand
   m,h; paddd acc,acc; pxor acc,m; paddw y,y`, 6 instructions for each of 16
   bits: 672, plus the lane arrangement and Karatsuba (about 200).
G. `Z ^= V_i & mask` with `V_i = H x^i`, `i < 8` (128 bytes of scratch) and
   `Z *= x^8` per byte: 128 x 5 + 16 x 8 = 770 and more for the masks (no
   `psrad`, `pcmpeq` or byte broadcast in the model).

E, F and G are within a fifth of each other on paper. E: its algebra is the
one RISC-V uses, it has most of its work in independent chains, and F's and
G's SIMD operations have fewer ports than the scalar ones (3 against 4).

Scratch (256 bytes): the key's 36 words of classes (144); 16 for the four
classes of the word being multiplied; `y` (16); the three products of 64
bits being combined and the three of 128 (48 + 32); 4 saved registers (16).
Registers: `ecx` scratch, `ebx`, `esi` the class sum, `edi` the y class,
`ebp`: data pointer; the count in memory. The product (64 bits) accumulates
as `lo`, `hi` in memory or in xmm (`movd`, `punpckldq`, `pxor`).

E, settled before its code: all scalar, in 32-bit words, as ARM's, so that the
same algebra serves both (ARM's word product is replaced by 16 `mul`s).
Reduction: `ror` by 1, 2 and 7 together are the shifts up and down by those
amounts at once, so `dn z = (ror sums) ^ up z`: 14 instructions for a word's
two folds, 4 words. Product: `mov eax,[y]; mov edx,[k]; mul edx; xor ebx,eax;
xor esi,edx`, the sum of a class in `esi:ebx`, the result in `ebp:edi`.
Scratch words: 36 key, 4 classes of the word multiplied, 4 of y, 12 of
products, 4 saved registers, pointer, count: 62 of 64. The words multiplied
are added up from y's when they are split.

# Hill-climbing (after the first measurement: x86 1.31, riscv64 1.044, arm 1.017)

## riscv64, about 515 instructions a block

* `li d, 0` and the first `xor d, d` of each of the nine products: the first
  class can be made in `d`. 18 fewer.
* The moves of `core` (`mv a4`, `mv s9`, `mv s4`, `mv s5`): give the products'
  destinations as parameters. 4 fewer.
* A class: `mul a6; mul a7; xor; mul a7; xor; mul a7; xor` waits for each
  `mul` in turn. Two accumulators: `mul a6; mul a7; mul r; xor a6 a7; mul a7;
  xor r a7; xor a6 r` needs one more register. Reused addresses: none.
* The loads of the block by bytes (44) stay: 8 + 7 + 7 is the least without a
  byte reversal or unaligned loads.

## arm, about 980 instructions a block, 243 `mul`

* Y is stored by `reduce` and loaded by the next `addX`: 8 of them can go if
  the loop's head gets it in registers, but `loadX` needs them for X; only
  4 loads (`eor` after `ldr`) stay. 
* count: `ldr, sub, str, cmp` can be one compare of the data pointer with its
  end: 3 fewer.
* classes of the key: 81 `and` again a block; 81 words of scratch do not fit.

## x86

Costs to measure rather than estimate, as prototypes in Rust intrinsics for
i686 (eight xmm registers), against the scalar code:

J. 16-bit lanes. Three levels of Karatsuba give 27 products of 16-bit words, in
   4 vectors (the last with 3 lanes). In a vector `w` of y's words the masks
   of the high byte's bits come first from `psraw(w, 15)` with `paddw w, w`
   between, then the low byte's; the sum byte's from `w ^ psllq(w, 8)` (junk
   below the byte is not read). The key's bytes, zero extended to 16 bits:
   `acc = acc + acc ^ (mask & k)`, eight times, gives a 15-bit product:
   6 instructions a step, of which 5 need a vector port, 96 steps: 480 over 3
   ports = 160 cycles, and Karatsuba and the reduction.
J2. Two (four) blocks at a time with `H^2 .. H`, one accumulator: the
   doubling of `acc`, Karatsuba's sums and the reduction shared. Key words
   (4 vectors each of three byte operands: 12 vectors of 16 = 192 bytes a
   power, or 4 and the bytes made on the way).
H. Byte lanes: not all of the bits of a lane's product fit; as J.
E2. Scalar, `mul`: 144 x (load, load, mul of 3 micro-ops, 2 xor) is bound by
   the front end (about 1350 micro-ops).

If J (about 165 cycles on paper) is not well under the scalar code's 230 when
measured, stop there.

## x86: J, measured, and the whole design

The core of J (96 steps and a stand-in for the recombination) as intrinsics on
i686: about 55 ns a block where the scalar code takes 92 and main 62. Go on.

Dwords of y: d0..d3 (d0 the low one). Nine dword products (Karatsuba twice):
d0..d3 (vector U0, as 8 words), and U1 = (d0+d2, d1+d3, d0+d1, d2+d3) =
pshufd(y,[0,1,0,2]) ^ pshufd(y,[2,3,1,3]), and all = d0+d1+d2+d3. A dword
product is three products of words: the two halves, lanes of U0 and U1, and
the sum: U2 = the sums of U0's halves in the even lanes, of U1's in the odd
ones. That is 24 lanes, three vectors exactly; `all` would take a fourth for
its three lanes, so it goes to the scalar code (16 `mul`, which use ports the
vectors leave idle).

A vector of eight 16x16 products: three times eight steps as above (high byte,
low byte, sum), mid ^= hi ^ lo; l = lo ^ (mid & ff) << 8; h = hi ^ (mid >> 8).
punpcklwd(l,h), punpckhwd(l,h): 32-bit products, pairs of them in a quadword as
P_lo + P_hi x^32, so X = [d0,d1], Y = [d2,d3], Z, W = [d0+d1, d2+d3]. U2's are
[d0,c0,d1,c1], [d2,w0,d3,w1] (dwords). fix(Q,S) = Q ^ (((Q ^ Q>>32 ^ S) << 32)
>> 16) by quadwords, S in the low dwords.
T = [X0+X1, Y0+Y1] + W; R0 = X ^ T0<<32, R1 = Y ^ T1<<32, mid = X^Y^Z ^
(T0^T1^Z0^Z1^V)<<32; R0 ^= mid<<64, R1 ^= mid>>64.
Reduction by quadwords: R0 ^= pslldq(dn R0, 8); out = R1 ^ R0 ^ up R0 ^
psrldq(dn R0, 8).
Scratch, 16 vectors: key bytes lo and hi of U0, U1, U2 (6; the sum's byte is
their XOR), key classes of `all` (1), y's classes (1), y (1), X Y Z W (4),
saved registers (1), pointer and count (1): 15.
Reversal of the bytes without pshufb: bytes of words by shifts of quadwords
and the mask 00ff, then pshuflw, pshufhw, pshufd: 9.

Measured (the prototype, intrinsics on i686, without the byte reversal): right
on a test against a bit loop, 51 to 54 ns a block; main 59 to 63; scalar 90 to
97. So this is the one to write. Word layout of scratch: keys 0-23 (vectors lo,
hi of U0, U1, U2), classes of `all` 24-27, y's classes 28-31, y 32-35, X 36,
Y 40, Z (first U1) 44, U2 48, saved 52-55, pointer 56, count 57, V 58-59, W 60.
Registers in a product of vectors: w xmm0, s xmm1, h xmm2, l xmm3, k xmm4,
xmm5, mask xmm6, 00ff xmm7.

J, as written: the scalar product stays in edi and ebp (no vector instruction
touches them) and goes to xmm6 by two movd and punpckldq before Karatsuba's
sums, rather than through memory, whose two stores a load of 16 bytes could not
be forwarded from. Pointer and count: words 56 and 57.

# Second round, settled before its code

## riscv64

As listed above: the first class of a product in its destination (2 fewer, nine
times), and the four moves of `core` removed by naming the products'
destinations (the sums' product in `s9 : a4`, the first's in `s4 : s6`, the last
fold into `s5`): 22 of about 515. `mulhu` with 64-bit words and five classes
would take 118 instructions a product of doublewords where this takes 139, but
the prepared form's key layout (32-bit words, four classes) is fixed by `Spec/`,
and two kinds of core are more to keep than it gains.

## arm

On Neoverse N2 (its software optimization guide): `mul` goes to one pipe (M0),
1 a cycle: 243 cycles a block, against about 980 / 5 = 196 for the width. An
operation with an operand shifted by more than 4 goes to the M pipes too (M0 or
M1, 2 cycles); each `classes` has three (`and d, mask, x, lsr #16`), 81 a block,
which take M0 from the `mul`s when the scheduler sends them there. A plain
shift is the integer pipes'. So the halves are made once (`lsl`, `lsr`) and the
classes are plain `and`s: 4 more instructions a 32-bit product (36 a block), 90
fewer operations for the M pipes. Other cores (Cortex-A53, A72): shifted
operands cost one more cycle of latency there too. Not done: storing the key's
classes (no scratch).
(arm, as written: the shift is the first instruction of `classes`, 27 more
instructions a block, 81 fewer for the M pipes; the sum's 9 shifted `eor`s stay.)
x86, J measured as emitted: 54 to 66 ns a block where main takes 51 to 66 on a
noisy host (the runs of both cluster at the same two frequencies); the alignment
of `scratch` changes 3%. The Benchmarks run decides.

# After the audit

x86 (32 bits) is main's code, which has no multiplication and was not to be
replaced: restored, unopened; everything above about x86 is moot.

riscv64, the registers of the key's preparation, from this code's own allocation
(they followed a list printed from the old proofs): masks in s0-s3 as in the
product; `H` in t1 and t2, its key in t4, t2 and t3, carries and halves in t5, t6,
t0 (the registers of the product's classes, all free before it); the temporary
is the product's first, a6.

## arm, third round (before its code)

Measured (run 45705935970): the plain shifts made it slower, 1.030 (16 KiB) where
the first code was 1.017. 27 instructions cost about 8 cycles a block: the width
(about 3 a cycle in A32) is the bound, not the multiplier. Back to the shifted
operands, and fewer instructions; the deficit, 11 cycles, is about 33 of them:

* The product of 32 bits: low, then sum, then high. The high half's product can
  be made in `lr`, which its classes read first, and the sum's stays in r0:
  2 fewer (a store and a load), nine times.
* The third product of doublewords (Karatsuba's outer middle) goes to the
  reduction in r6-r9: 2 stores and 4 loads fewer.
* Y stays in registers from the reduction (r0, lr, r10, r11) to the next block's
  addition: 4 stores and 4 loads fewer.

32 fewer in all.

riscv64, measured (run 45705935970, its earlier prep registers): the interleaved
rounds' medians 1.026 at 16 KiB, single estimates 1.012; 64 B 1.00 to 1.03; 1 MiB
0.995; GCM-SIV 0.999 to 1.034. Left: 64-bit words and five classes with `mulhu`
(about 60 fewer of 493 instructions, but another 29 registers' allocation, and the
prepared form's table is fixed as 32-bit words). Not done.
