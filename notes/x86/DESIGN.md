# Bitsliced AES on 32-bit x86 (SSE2): design, written before the code

Sources: FIPS 197, the repository's x86 model and StraightX/StraightSse evaluators (which, unlike
x86-64's, follow whole 128-bit registers), the lead's DESIGN.md, Circuit.lean and x86-64 Sse.lean.
Recognised ideas: semi-fixslicing (Adomnicai-Peyrin), as the lead notes; the Boyar-Peralta tower
circuit (the lead's); swapmove transposes; 63 in the round keys.

Constraints: 8 xmm registers, two-operand, no memory operands (loads are instructions), no pshufb,
no byte or word shifts (pslld/psrld/psllq/psrlq/psraw), no byte unpacks; pshufd, pshuflw, pshufhw and
punpck{wd,dq,qdq} exist. 2048 bytes of scratch.

## Layout
Slice j, 128 bits, index bits (low to high) [k0 k1 k2 c0 c1 r0 r1]: bit j of row r, column c of
block k at 8 (c + 4 r) + k. A row is a dword, a column a byte of it.
 * next row: pshufd 0x39; two rows on: pshufd 0x4E (1 each, non-destructive, so they save the copy)
 * all rows' columns by one: dword rotate by 8 (psrld, pslld, pxor: 3 and a copy); by two:
   pshuflw 0xB1 + pshufhw 0xB1
 * ShiftRows twice (odd rows by two columns): words of dwords 1 and 3 swapped: pshuflw 0xB4 +
   pshufhw 0xB4, 2 instructions and no mask.
The other layout, [k k k r0 r1 c0 c1] (no byte transposition), would cost 12.5 a slice and round
against 9.

## Linear layers (per slice; b = a ^ next a; out = 2b ^ next a ^ row2 b)
 * round A (form 0 in, 1 out): v = pshufd a; copy, psrld, pslld, pxor (5); pxor b; pshufd, lw, hw of
   b (3); pxor; +1.. : 11, 91 a state.
 * round B (form 1 in, SR^2, plain): lw, hw (2); pshufd, pxor, pshufd, pxor, pxor: 7, 59 a state.
 * key: load and pxor, 16.
 * inverse: a ^= 4 (a ^ row2 a) first: 29 (form 0) / 45 (form 1) more.
Rounds: A, then (Nr/2 - 1) x (B, A), then SubBytes, SR^2, out. Inverse: DA (SR^2, ISB, key, IMC form 1),
then (Nr/2 - 1) x (DB (ISB, key, IMC form 0), DA), ISB, out.

## S-box
Lead's 112/113-gate circuits (no constants). Ordered and allocated by annealing (alloc.cpp) to 8
registers: from all inputs in slots to outputs anywhere: 197 instructions forward (51 loads, 25
stores, 10 copies), 203 inverse so far.
Round: about 197 + 91 + 32 = 320 (A), 197 + 59 + 32 = 288 (B); joint allocation of a whole round
(S-box and linear layer together) gains only 1-3%, so the two are separate blocks.

## Bytes to slices
Blocks x_k, index bits [j0 j1 j2 r0 r1 c0 c1 ; k]. Whitening with the plain round key 0 (and the last
round key) on the bytes, so only Nr-1 keys are bitsliced. Per pair of registers (N0 = k0), word level
by punpck (3 instructions a pair): wd: P4<-N, P5<-P4, P6<-P5, N<-P6; dq: P5<-N, P6<-P5, N<-P6; qdq: P6<->N.
 wd, wd -> [.. r0 | c1 k0 r1 ; c0]; swapmove of bytes (P3 <-> N0) -> P3 = c0, N0 = r0; dq, qdq ->
 [c0 c1 r0 r1 ; k0]. 12 + 7 a pair. Then j0,j1,j2 <-> k0,k1,k2, 12 swapmoves. In two groups of four
registers (k0, k1) and then four pairs (k2), through slots: about 210 each way.

## Round keys
128 bytes a key, 1..Nr-1, at most 13 * 128 = 1664: a slice is its 16 bytes 00/FF. Setup a key: bytes
permuted to row-major order (swap word bits by shuffles 4, one in-register swapmove 7; odd keys with
row r rotated r columns), then a tree of masks and shifts duplicates bit j over each byte:
(2 + 4 + 8) x 5: about 85 a key. 63 added to keys 1..Nr: complement slices 0,1,5,6; the last key's
bytes ^ 63 in a slot.

## Scratch (16-byte slots, edx): 0-7 the batch's blocks, then its state; 8-.. S-box spills; masks;
the plain key with 63; saved registers; keys from 384 on (eax walks them).

## Functions
batch: 8 blocks in slots 0-7, in place; blocks and CTR copy in and out (partial batches need no more).
CTR: counter blocks written to the slots, the key stream XORed from src to dst.

## Key expansion (GPR): slices are w >> j, circuit with memory operands, bits gathered by Horner
doubling. No transposition.
