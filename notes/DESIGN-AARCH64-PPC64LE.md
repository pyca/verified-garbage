# Clean-room bitsliced AES, AArch64 and PPC64LE: decided before the code

Sources: FIPS 197, the ISA models, the lead's DESIGN.md (bench/aes-cleanroom-notes: S-box circuits,
64-bit layout, skipped ShiftRows) and its x86-64 code. Removed files, their history and main's
generated code were not looked at. Standard ideas recognised: swapmove / bit-matrix transposes by
index-bit exchange, skipping ShiftRows ("fixslicing", as the lead says), nibble lookup by `tbl`.

## NEON, 8 blocks, 128-bit slices
Byte p of slice j holds bit j of byte p of blocks 0..7 (bit k: block k): [k k k r r c c ; j].
From 8 registers of 8 blocks this is an 8x8 bit transpose in each byte column, three exchanges.
 * nibbles: `mov t,a; sli a,b,#4; sri b,t,#4` (3 ops a pair; .16b forms keep bytes apart)
 * pairs, bits: `ushr t,a,#n; shl u,b,#n; bif a,u,m; bit b,t,m` (4 ops)
 44 ops in place, 12 fewer masks than xor-swapmove (72). The inverse is the same three exchanges.
 Everything is bytewise, so the proof evaluates one byte column: 8 words of 8 bits.
SubBytes: the lead's circuits, 112 (forward, without its constant) and 113 (inverse) gates; NEON is
 three-operand, ordered (own search) for 25 live values: v0-v24, no spills. v25-v31 hold constants.
ShiftRows + MixColumns literal: t = tbl(a, SR then rot1); a = tbl(a, SR); a ^= t (b);
 o = t ^ rev32.8h(b) ^ b_{j-1}: 6 ops a slice + 3 = 51. (Skipping ShiftRows would save 4 a round on
 average, not worth four forms.) Last round: 8 tbl.
InvMixColumns: x = a ^ 4 (a ^ rot2 a), then MixColumns: 16 + 15 + 43; InvShiftRows 8 tbl.
Round keys are not bitsliced in memory. Slice j of a round key is 00/ff a byte: look the byte's
 nibbles up in T_j (byte i = ff if bit j of i): K ^= 63; lo = K & 0f; hi = K >> 4;
 s_j ^= tbl(T_j, lo), s_{j+4} ^= tbl(T_j, hi): 3 + 16 ops and a load per round, no key setup, no
 scratch (against 16 + 8 loads, 1920 bytes and about 24 ops a round key of setup).
 {63} goes into round keys 1..Nr as in the lead's notes (MixColumns and ShiftRows fix it).
Registers: v0-v24 state/S-box; v25 SR, v26 SR+rot1 (forward) or v25 InvSR, v26 rot1 (inverse),
 v27-v30 T_0-T_3, v31 63; 0f in a scratch slot, reloaded after MixColumns. Constants made by
 movz/movk/dup/ins at entry: no statics. v8-v15 saved in scratch.
About 182 vector ops a round, 1900 for 128 bytes of AES-128.
Same batch for fewer than 8 blocks (missing ones are copies of whatever is there, not written).
CTR: 8 counters by add.4s on byte-reversed words, rev32.

## Scalar (only without AdvSIMD), 4 blocks, 64-bit slices: the lead's Slices.lean layout
[k k c0 c1 r0 r1]; rotates are free in an operand.
 * MC form 0: t = a ror 16; b = a ^ t; o = t ^ b ror 32 ^ b_{j-1}: 3-4 ops a slice + 3.
 * form 1: t = (a ror 20)&M | (a ror 4)&~M, rot2 likewise: 9 a slice + 3.
 * SR^2: t = (a ^ a ror 8) & m; a ^= t; a ^= t ror 56.
 * transposes by the lead's six exchanges, 4 ops a swapmove: eor t,hi,lo ror n; and; eor; eor ror.
 * round keys: 64 bytes each, 8 dwords, complemented in slices 0,1,5,6, odd ones in form 1.
Key expansion: SubWord with no transpose (lead): slices w >> j, S-box, gather the 4 bits.

## SM4, Camellia, SEED (AArch64 scalar, PPC64LE): ortho = 8x8 transpose of 8 dwords per byte
 (exchanges of word-number bits with in-byte bits), the same interface as the lead's x86-64 Linear
 (ortho, zip1, zip2, swap8). AArch64 4 ops a swapmove; PPC64LE 6 (rotldi, xor, and, xor, rotldi, xor).
