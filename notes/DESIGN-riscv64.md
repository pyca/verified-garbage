# Clean-room bitsliced AES on RISC-V (RV64IM): design, written before the code

Sources: FIPS 197; TCB/RISCV64/Isa.lean; the lead's notes (bench/aes-cleanroom-notes,
notes/DESIGN.md), Impl/Aes/Circuit.lean and its x86-64 files on claude/cleanroom-aes-bitsliced.
Seen before this was written, besides those: Impl/Aes/RISCV64/{Alloc,Blocks,Chain,Fn}.lean, the
unlisted files left in the tree for this target (loops and names of layers; the bodies of the
layers are not in them). From them: the scratch buffer's base is `sb` (a5), keys are bitsliced
once a call in 64 bytes a round, `kp` walks them, four blocks enter as dwords, q b / q (b+4).

## Layout
64-bit words, four blocks; slice j holds bit j of every byte, the byte (r, c) of block k at
k + 4 (c + 4 r) (the lead's [k k c0 c1 r0 r1]): Proof/Aes/Slices.lean as is. A row rotation is
a rotation by 16: srli, slli, or = 3. No rotate instruction in the model.
toBs: dwords q b = columns 0,1 of block b, q (b+4) = columns 2,3, i.e. register k + 4 c1; six
exchanges (register-number bit, position bit): (2,3) (2,4) (2,5) (2,2) (1,1) (0,0), each 4
swapmoves of 6 (three-operand: t=lo>>n, t^=hi, t&=m, hi^=t, t<<=n, lo^=t): 144. It is the fewest:
the bits j0 j1 j2 r0 r1 c0 and the three word-number bits all move, in at most three cycles
through a word-number bit, 9-3 = 6. (Loading bytes one at a time could put r on top for nothing,
3 exchanges, but costs 22 operations a dword against 1.)

## Registers
Public: a0 schedule, a3 data, a4 blocks left, a5 scratch, kp (round key). Slices in eight
registers, the S-box to the same eight; all other registers free for the circuit (about 22 in
all). Masks are kept in slots of the scratch buffer (a load a pass) or registers where free.

## Rounds
Fixslicing with two forms, as the lead has it (the name is Adomnicai and Peyrin's; the derivation
in the lead's notes is from FIPS 197):
 round A (form 0 -> 1): S0, MC in form 1 (next row one column further), key form 1
 round B (form 1 -> 0): S0, SR^2, plain MC, key form 0
Per slice: rowrot 3, column rotation 5 with one mask ( ((z>>4 ^ z<<12) & m) ^ z<<12 ).
 MC plain: b=a^rot1 a (4), rot1 a ^ rot2 b (4), ^ b_{j-1} (1): 9, 75 a state with the reduction
 MC form 1: 4+5, 4+5, 1 = 19, 155 a state
 SR^2: t=(x>>8 ^ x)&m; x^=t; x^=t<<8: 6, 48 a state
 so 155 in A, 123 in B: 139 a round; literal ShiftRows (13 a slice) would be 179.
Structure: A; loop {B; A}; last (S0, SR^2, key): Nr is even. Four forms (1,2,3,0; no SR^2 but at
the end: per slice 16, 11, 16, 6 against 16, 12, 16, 12) would save about 112 of 2900
instructions a batch, for seven rounds of code rather than three and a half: tried afterwards.
S-box: the lead's circuit without its constant (112 gates, three operands, no moves); {63} is
added to the round keys 1..Nr instead.
Inverse: SR^2, I0 (113 gates), key form 1, InvMC form 1; I0, key form 0, InvMC form 0; last
without InvMC. InvMC a = MC (a ^ 4 (a ^ rot2 a)): first step 4 (form 0) or 9 (form 1) a slice
plus 13 for the multiplication by 4: 45 / 85 a state.

## Round keys
64 bytes each (a dword a slice, the same in the four blocks), ld + xor: 16 a round.
 * Plain way: one key a time through toBs: about 190 a key with the form and the complement.
 * Four keys at once as the four blocks of one toBs (144), odd keys to form 1 by one ShiftRows
   with masks of their nibble bits (13 a slice), then each spread to four blocks
   ((x >> k) & 0x1111.. = t, (t << 4) - t) and stored: 440 a group, 110 a key.
   Groups start at odd keys: 1, 5, ... and last Nr-3 (overlapping the one before), so no partial
   group and no read past the schedule.
 * Key 0 could be XORed to the dwords before toBs: 10 rather than 16, and once a call in CTR.
Use whichever the block, CTR, chaining and GCM code that shares the key setup can take.

## Counts (instructions), AES-128, four blocks
toBs 144, keys 11x16, S-box 10x112, MC/SR^2 5x155+4x75+5x48, fromBs 144: about 2900, 725 a block.

## Key expansion
SubWord on one word: slice j = w >> j (junk in other bits is harmless), circuit, gather
sum (s_j & 0x01010101) << j, ^ 0x63636363: 7 + 112 + 22 + 1.

## SM4, Camellia, SEED
Byte <-> slice transposes of 8x8 bit matrices: three passes of four swapmoves, 72 instructions;
other byte permutations as their code (unlisted) asks for.
