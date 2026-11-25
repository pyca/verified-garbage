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
