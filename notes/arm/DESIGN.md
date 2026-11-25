# Bitsliced AES on 32-bit Arm: design, written before its code

Sources: FIPS 197; TCB/Arm/Isa.lean; notes/DESIGN.md (the lead's) and its Circuit.lean and
x86-64 layers. Not read: the removed files, their history, main's generated code; of the
remaining Arm files only names and `import` lines. The order of the representations below is
"fixslicing" (Adomnicai and Peyrin), which the lead's notes name and derive from FIPS 197;
I know the published method too, and that its Arm version exists, but not its code; what is
below is derived from the representation's definition.

## Layout
Two blocks in eight 32-bit slices: bit j of the byte in row r, column c of block k at bit
k + 2 c + 8 r of slice j. A row is a byte, so a row rotation is `ror #8`, free in an operand.
In form i (0..3) the byte (r, c) is at column c + i r. ShiftRows is never done: a round goes
from form i to form i + 1 mod 4, the inverse cipher's from i to i - 1. The round key of round j
is stored in form (s + j) mod 4, s = -Nr mod 4 (2 for 10 and 14 rounds, 0 for 12), so that the
cipher always ends in form 0 and the same keys serve both directions. The input is loaded in
form s (for s = 2 an exchange of halves of the odd rows' bytes: 4 a slice, or 8 on the four
words of a block before the transpose).
`toBs`: words c + 4 k -> index bits j0<->k0, j1<->c0, j2<->c1: 12 swapmoves of 4 (eor lsr; and;
eor; eor lsl) = 48, masks 6.

## MixColumns in form i
f = rows by 1 and columns by i. b = a ^ f a; out = 2 b ^ f a ^ f^2 b.
C1 (columns by one) : and t, m, a, lsr #2; bic u, a, m, lsl #2; orr t, t, u, lsl #6, m = 3f3f3f3f.
C2: and t, n, a, lsr #4; and u, a, n; orr t, t, u, lsl #4, n = 0f0f0f0f. C3 is C1 backwards.
Per slice: form 0: 3 (b; out = b' ^ a ror 8; out ^= b ror 16). Form 2: 6 (C2 3, then 3).
Forms 1, 3: 9 (C1 3; 2; C2 of b folded: bic, and, two eor with rotations ror 20, ror 12).
out_j accumulates in b_{j-1}'s register; b7 stays until slice 4 (reduction: 3 more XORs).
Registers: 8 slices + b7's displacement 2 + temporaries 2 + masks 2 = 14 with the base: one
too many, so forms 1, 3 spill one value (2 instructions).
Whole: 27, 81, 53, 81 (with the masks) = 242 for four rounds.
InvMixColumns = MC(a ^ 4 (a ^ f^2 a)): first part 8 + 13 (forms 0, 2) or 32 + 13 (+ masks).

## Round loop (encryption); rem = Nr, then rounds left
 ARK; do { if rem & 2 = 0 { SB MC1 ARK SB MC2 ARK; rem -= 2 }; SB MC3 ARK; SB; rem -= 2;
 if rem != 0 { MC0 ARK } } while rem != 0; ARK. (MCi: in form i, after the S-box of the round
 that ends in form i.) The last round's missing MixColumns is the mid-body exit.
Decryption: ARK(Nr); do { [InvSR free: form 3] InvSB ARK InvMC3; InvSB ARK InvMC2; if rem & 2
 ... } mirrored.
AddRoundKey: 8 ldr + 8 eor, + 1 ldr of the key's pointer (kept in a slot).
The S-box's {63} is in round keys 1..Nr (MixColumns and ShiftRows fix the constant vector), as
on x86-64; I recognise this from other bitsliced implementations too.

## S-box
Circuit.sbox, 112 gates, three-operand instructions: 112 + spills, 13 registers besides the
scratch base; a search for the order and the registers, inverse 113 + spills.
Estimate for spills 30 to 40 loads and stores. Round: about 112 + 35 + 61 + 17 + 2 = 227.

## Round keys
Plain bytes in the schedule. One round key at a time: 4 words; + {63}; into form i on the words
(rows 2,3 by two columns: exchange of halves; rows 1,3 by one: masked: 0, 21, 8, 21 instructions);
4 swapmoves exchange j1<->c0, j2<->c1; then each word holds two slices in its even and odd bits,
which are spread over both blocks' bits: e = w & 55..; e | e<<1; o = w ^ e; o | o>>1: 16.
About 60 a round key, 8 words (32 bytes) each, 480 bytes at most.

## Key expansion
SubWord: slice j = w >> j (junk elsewhere is harmless), S-box, sum (slice j & 01010101) << j,
^ 63636363. About 8 + 147 + 17.

## Counter blocks
Two counter blocks at a time; partial last group by the same code on a buffer.
Scratch: keys (480 B), spills, masks' none (made by movw/movt), counters and saved pointers.

SM4, Camellia, SEED: same `toBs`-like transposes (exchanges as above); S-box circuits to be
looked at after this is committed.

## Final counts (added after the code)

S-box 132 instructions (112 gates, 9 stores, 9 loads, 2 sums recomputed), inverse 133;
in place in 12 registers (key expansion's shared form) 141.
Found by: `lp.cpp`/`combo.py` (equal-size linear layers for the same targets),
`sched3.cpp`/`sched4.cpp` (simulated annealing over orders with Belady eviction; sched4 may
also recompute a wire as the sum of any two live ones), `alloc*.py` (register colouring that
fixes the outputs to p 0..7).
MixColumns per form 28/79/54/79; InvMixColumns 49/124/75/124; four rounds 842.
