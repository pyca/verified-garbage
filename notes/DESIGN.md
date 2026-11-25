# Clean-room bitsliced AES: working, written before the code

Sources: FIPS 197; the repository's ISA models; Boyar & Peralta, "A New Combinational
Logic Minimization Technique with Applications to Cryptology" (SEA 2010, the NIST-hosted
PDF, pub_id 902701): its tower-field split (top linear / 32-AND middle / bottom linear),
its Fig. 2 (GF(2^4) inversion) and its linear-program heuristic. No listing of a whole
S-box was used: `sbox_search.cpp` enumerates tower bases itself and `sbox_check.py` checks
each result on all 256 inputs.

## S-box
`results/fwd-112.txt`: 112 gates (32 AND, 80 XOR), constant 0x63 added on 4 outputs.
Inverse: same search with U composed with aff^-1 and B without aff: `results/inv-115.txt`.
Both searches still run; the final pick also weighs spills per target.

## Layout
Word of 16*B bits (B = 8, 4, 2 blocks per word); slice j holds bit j of every byte;
byte p of the state is the group of B bits at lane pi(p), bit k of the group is block k.
Write index bits: in-word (low to high) ; word number. A load of plain bytes gives
 * 128-bit, 8 regs = 8 blocks:  [j0 j1 j2 r0 r1 c0 c1 ; k0 k1 k2]
 * 64-bit, 8 regs = 4 blocks:   [j0 j1 j2 r0 r1 c0 ; c1 k0 k1]
 * 32-bit, 8 regs = 2 blocks:   [j0 j1 j2 r0 r1 ; c0 c1 k0]
An exchange of a word-number bit with an in-word bit is 4 swapmoves (3 logic + shifts).
 * 128: exchange j0,j1,j2 with k0,k1,k2 -> [k k k r0 r1 c0 c1 ; j]. 12 swapmoves. A column
   is a 32-bit lane: rows rotate by a dword byte rotate, columns by pshufd.
 * 32: exchange j0<->k0, j1<->c0, j2<->c1 -> [k0 c0 c1 r0 r1 ; j]: a row is a byte, row
   rotation = ror #8 (free in an Arm operand). 12 swapmoves.
 * 64: want r0 r1 on top (a rotate by 16): [k k c0 c1 r0 r1]. c0:P5->P2, r1:P4->P5, r0:P3->P4,
   c1:W->P3, j2:P2->W is one 5-cycle through the word-number bit, 4 exchanges; with the two k
   exchanges 6 in all (24 swapmoves) against 3 (12) for [k k c1 r0 r1 c0] where a row rotation
   is mask/shift in each 32-bit half. Per slice and round the first layout saves 4 ops (RISC-V,
   no rotate) to 8 (x86): worth 144 ops once.

## ShiftRows and MixColumns
Let rot1/rot2 move every byte up 1/2 rows in its column. MixColumns per slice (FIPS 5.1.3):
b = a ^ rot1 a; out = 2b ^ rot1 a ^ rot2 b, 2 rotations, 3-4 XORs, 3 more XORs per state for
x^8 = x^4+x^3+x+1.
ShiftRows done literally costs, per slice: 13 (32- and 64-bit, masks and shifts), >= 12 (SSE2,
no byte shuffle), 1 (NEON tbl).
Alternative: do not move bytes; keep (r,c) at (r, c+i*r) after i skipped ShiftRows. Then rot1
must also move columns by i for ALL rows (uniform), rot2 by 2i. With i in {0,1} and a physical
SR^2 (odd rows move two columns: an exchange of halves) every second round:
 round A (rep 0 -> 1): SB, MC with (r+1,c+1),(r+2,c+2); key K'(r,c+r)=K(r,c)
 round B (rep 1 -> 0): SB, SR^2, plain MC; key plain
Nr is 10, 12 or 14, so rounds pair up; the last pair's B has no MC and ends in rep 0.
Inverse (down from rep 0): InvSR,: SR^2 takes rep 0 to rep 1 (InvSR T stored at (r,c+r) is
T(r,x-2r)), InvSB, key rep 1, InvMC in rep 1; next InvSR takes rep 1 to rep 0 for nothing.
So the same stored keys serve both directions.
Per slice (avg of A and B), against literal SR:
 * SSE2: shuffle parts 10 + SR^2 4 in B -> MC+SR about 16, literal about 26
 * 32-bit Arm: A 9 (col rotate = and/and/orr), B 7 -> 8, literal 16
 * 64-bit RISC-V: rot1=3 (+5 for a column), A 3+5+3+5, B 3+3+6 -> avg 14+4 XOR, literal 23
 * NEON: literal (tbl merges SR with rot1): 3 shuffles + 3 XORs.
(I also recognise this as "fixslicing", a published method of Adomnicai and Peyrin; the
derivation above is from FIPS 197 alone.)
InvMixColumns: d(x) = a(x)(4x^2+5) mod x^4+1, so InvMC(a) = MC(a ^ 4(a ^ rot2 a)).

## Round keys
Plain bytes in the schedule. 128-bit: pairs of slices share a vector (low nibble of each byte
= slice j, high nibble = slice j+4): 64 bytes a round key; a whole round key in 8 vectors
would need 15*128 = 1920 bytes of scratch, more than the callers leave (1480).

## Key expansion
SubWord needs only 4 bytes = bits 0,8,16,24 of a word. No transpose: slice j is w >> j (the
S-box is bitwise, so junk in other bits is harmless); afterwards sum over j of
(slice j & 0x01010101) << j. About 16 + S-box + 24 ops.

## Counter blocks
CTR32: 8 counter blocks per batch, block k = nonce words with the last word
bswap(ctr + k); only bytes 12..15 differ. Build the blocks in memory or lanes, encrypt, XOR
into data, partial last batch by whole-block loop.

## Plan per target
x86_64, x86: one SSE2 engine (8 blocks) for CTR and blocks; aarch64: NEON; arm: 32-bit;
riscv64: 64-bit; powerpc64le: only the byte<->slice transpose and circuit (for SM4, Camellia,
SEED), AES itself uses vector crypto there.
