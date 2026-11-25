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
