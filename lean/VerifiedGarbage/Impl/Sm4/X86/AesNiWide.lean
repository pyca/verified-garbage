module

public import VerifiedGarbage.Impl.Sm4.X86.AesNi
public import VerifiedGarbage.Impl.Sm4.X86.Ecb
public import VerifiedGarbage.Impl.Modes.X86.Wide

/-!
# SM4 on x86 (32-bit) with its S-box by `aesenclast`: four blocks at a time

The round of `AesNi.lean`, with a word of four blocks in a register: a
block's word in each of the four 32-bit lanes, its bytes in the block's
order, kept as `PL X` as there. Every instruction of that round acts on each
lane alone but `aesenclast`, whose ShiftRows moves a byte to the same byte
of another lane: a shuffle that undoes it (`oISR`) goes before it, and the
round is otherwise the one-block round. The round keys have the one-block
core's form, `PK rkᵢ` in every lane, in the same places of the scratch
buffer.

`prepare d` and `crypt` are a core of the modes (`core d`,
`Impl.Modes.X86.Core`) for four blocks at a time, in the direction `d`. With
the modes' scratch buffer at `sb`: its first slot holds the address of the
table of constants `VG_SM4_AESNI_WIDE` (the one-block core's, and the
shuffle), the ring of the state's four words is at byte 32 (a place holds a
word of the four blocks), the round keys from byte 96 on, and the four
blocks at byte 624 (`oB`).

* `prepare d` stores the round keys in the order the rounds read them: the
  schedule's order for encryption, and the reverse for decryption (GB/T
  32907-2016 §7.2), for which the keys' pointer goes down from the last
  four places, and a group's four keys are stored last to first. It reads
  the key through the first stack argument alone.
* `crypt` takes the four blocks into the rounds' form, a block in a
  register, and transposes the four registers' doublewords (`transpose`),
  which gives the four words, each of the four blocks; after the 32 rounds
  the four words of the ring, the last first, out of the rounds' form, are
  transposed back to the four blocks. It enciphers the buffer's four
  blocks whatever the number of them a mode's step uses.

The code is `aes` and `ssse3` code: its dispatcher runs it only where the
CPU has both.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86.AesNiWide

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)
open VG.Impl.Sm4.X86.AesNi (oM0 oE oH oBR oCV oIV oK oBSW tbr kr oR m0 x ld stx)

/-- The table of constants' name. -/
def tableName : String := "VG_SM4_AESNI_WIDE"

/-- The constants: the one-block core's, and the shuffle that undoes
`aesenclast`'s ShiftRows. -/
def table : List (BitVec 64) := AesNi.table ++ [0x0b0e0104070a0d00, 0x0306090c0f020508]

/-- The inverse of ShiftRows, as a shuffle. -/
def oISR : Nat := 240

/-- The four blocks in the scratch buffer. -/
def oB : Nat := 624

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table

/-- The byte map at `t` (`oCV`, `oIV` or `oK`) of every byte of `v`, to
`b`; `v`, `a` and `c` are lost. -/
def conv (v a b c : XReg) (t : Nat) : List Instr :=
  [x .movdqa a v, .xop (.shift .psrld a 4), x .pand a m0, x .pand v m0,
   tb b t, x .pshufb b v, tb c (t + 16), x .pshufb c a, x .pxor b c]

/-- A round but its first instruction, which loads the next round's key to
`e`, and its last, which stores the new word (`AesNi.roundX`, with the
shuffle before `aesenclast`): `aesenclast`'s input is in `a` and the newest
word in `n`, the round's oldest word at `s0` of the scratch buffer and its
third at `s2`; the next round's input is left in `c` and the new word in
`e`. -/
def roundX (a c n e : XReg) (s0 s2 : Nat) : List Instr :=
  [ld .xmm6 sb s2, x .pxor e .xmm6, x .pxor e n,
   ld .xmm3 sb s0, x .pxor .xmm3 e,
   tb .xmm6 oISR, x .pshufb a .xmm6,
   x .aesenclast a m0,
   x .movdqa n a, x .pand n m0, .xop (.shift .psrld a 4), x .pand a m0,
   tb c oE, x .pshufb c n, tb .xmm5 oH, x .pshufb .xmm5 n, x .movdqa n c,
   tb .xmm6 (oE + 16), x .pshufb .xmm6 a, x .pxor c .xmm6, x .pxor n .xmm6,
   tb .xmm6 (oH + 16), x .pshufb .xmm6 a, x .pxor .xmm5 .xmm6,
   x .pxor .xmm3 c, x .pxor .xmm3 .xmm5,
   tb .xmm6 oBR, x .pshufb c .xmm6, tb a (oBR + 16), x .pshufb n a, x .pxor c n,
   tb .xmm6 (oBR + 32), x .pshufb .xmm5 .xmm6, x .pxor .xmm3 .xmm5,
   x .pxor c .xmm3,
   x .pxor e c]

/-- Round `j` of a turn (0 to 3): its oldest word is in the ring's place
`j`, where its new word goes, and its third in place `(j + 2) mod 4`; the
next round's key is the one after its own, at `kr + 16 j + 16`. -/
def round (a c n e : XReg) (j : Nat) : List Instr :=
  [ld e kr (16 * j + 16)] ++ roundX a c n e (oR + 16 * j) (oR + 16 * ((j + 2) % 4)) ++ [stx sb (oR + 16 * j) e]

/-- On by four keys; a turn fewer. -/
def step : List Instr := [.alu .add kr (.imm 64), .alu .sub .eax (.imm 1)]

/-- A turn of the loop, four rounds: from `xmm0` and `xmm1` to `xmm4` and
`xmm2`, and back, twice. -/
def turn : List Instr :=
  round .xmm0 .xmm4 .xmm1 .xmm2 0 ++ round .xmm4 .xmm0 .xmm2 .xmm1 1 ++ round .xmm0 .xmm4 .xmm1 .xmm2 2 ++
    round .xmm4 .xmm0 .xmm2 .xmm1 3 ++ step

/-- The 4 × 4 doublewords of `xmm0` to `xmm3` transposed: doubleword `i` of
each, in their order, to `xmm0`, `xmm3`, `xmm4` and `xmm1` for `i` from 0 to
3; `xmm2` and `xmm5` are lost. -/
def transpose : List Instr :=
  [x .movdqa .xmm4 .xmm0, x .punpcklqdq .xmm0 .xmm1, .xop (.pshufd .xmm0 .xmm0 0xd8),
   x .punpckhqdq .xmm4 .xmm1, .xop (.pshufd .xmm4 .xmm4 0xd8),
   x .movdqa .xmm5 .xmm2, x .punpcklqdq .xmm2 .xmm3, .xop (.pshufd .xmm2 .xmm2 0xd8),
   x .punpckhqdq .xmm5 .xmm3, .xop (.pshufd .xmm5 .xmm5 0xd8),
   x .movdqa .xmm3 .xmm0, x .punpcklqdq .xmm0 .xmm2, x .punpckhqdq .xmm3 .xmm2,
   x .movdqa .xmm1 .xmm4, x .punpcklqdq .xmm4 .xmm5, x .punpckhqdq .xmm1 .xmm5]

/-- Block `j` of the buffer, in the rounds' form, to `r`. -/
def blockIn (j : Nat) (r : XReg) : List Instr := [ld .xmm4 sb (oB + 16 * j)] ++ conv .xmm4 .xmm5 r .xmm6 oCV

/-- The four blocks to their four words in the rounds' form, in `xmm0`,
`xmm3`, `xmm4` and `xmm1`, and the exclusive-or of the last three in
`xmm2`. -/
def headX : List Instr :=
  [tb m0 oM0] ++ blockIn 0 .xmm0 ++ blockIn 1 .xmm1 ++ blockIn 2 .xmm2 ++ blockIn 3 .xmm3 ++ transpose ++
    [x .movdqa .xmm2 .xmm3, x .pxor .xmm2 .xmm4, x .pxor .xmm2 .xmm1]

/-- Four registers to four places of 16 bytes of the scratch buffer, from
byte `o` on. -/
def stores (o : Nat) (r0 r1 r2 r3 : XReg) : List Instr :=
  [stx sb o r0, stx sb (o + 16) r1, stx sb (o + 32) r2, stx sb (o + 48) r3]

/-- The table's address, the keys' pointer and the eight turns. -/
def cryptRegs : List Instr :=
  [.mov tbr (.mem (at_ sb 0)), .mov kr (.reg sb), .alu .add kr (.imm 96), .mov .eax (.imm 8)]

/-- The first round's key. -/
def cryptKey : List Instr := [ld .xmm0 kr 0, x .pxor .xmm0 .xmm2]

/-- The buffer's four blocks to the ring, and the first round's input. -/
def cryptHead : List Instr := cryptRegs ++ headX ++ stores oR .xmm0 .xmm3 .xmm4 .xmm1 ++ cryptKey

/-- The ring's place `3 - j`, out of the rounds' form, to `r`: word `j` of
the four blocks. -/
def wordOut (j : Nat) (r : XReg) : List Instr :=
  [ld .xmm4 sb (oR + 16 * (3 - j))] ++ conv .xmm4 .xmm5 r .xmm6 oIV

/-- The last four words (the ring's), the last first, to the four blocks'
bytes: in `xmm0`, `xmm3`, `xmm4` and `xmm1`. -/
def tailX : List Instr :=
  wordOut 0 .xmm0 ++ wordOut 1 .xmm1 ++ wordOut 2 .xmm2 ++ wordOut 3 .xmm3 ++ transpose

/-- The last four words to the buffer's four blocks. -/
def cryptTail : List Instr := tailX ++ stores oB .xmm0 .xmm3 .xmm4 .xmm1

/-- The four blocks of the core's buffer, enciphered in place. -/
def crypt : Prog isa :=
  .seq (.block cryptHead) (.seq (.loop (.block turn) .ne) (.block cryptTail))

/-- Where the keys' pointer starts in `prepare`: the first four places, or,
for decryption, the last four. -/
def keyBase : Dir → Nat
  | .encrypt => 96
  | .decrypt => 544

/-- The lane of the group's key that goes to the place at `kr + 16 w`: the
keys in their order, or, for decryption, the last first. -/
def keyLane : Dir → Nat → BitVec 8
  | .encrypt, w => BitVec.ofNat 8 (0x55 * w)
  | .decrypt, w => BitVec.ofNat 8 (0x55 * (3 - w))

/-- Four round keys of the schedule (at `eax`), in the rounds' form, to
the four places at `kr`. -/
def prepGroupX (d : Dir) : List Instr :=
  [ld .xmm0 .eax 0, tb .xmm1 oBSW, x .pshufb .xmm0 .xmm1] ++ conv .xmm0 .xmm1 .xmm2 .xmm3 oK ++
    [.xop (.pshufd .xmm3 .xmm2 (keyLane d 0)), stx kr 0 .xmm3, .xop (.pshufd .xmm3 .xmm2 (keyLane d 1)),
     stx kr 16 .xmm3, .xop (.pshufd .xmm3 .xmm2 (keyLane d 2)), stx kr 32 .xmm3,
     .xop (.pshufd .xmm3 .xmm2 (keyLane d 3)), stx kr 48 .xmm3]

/-- The keys' pointer to the next four places. -/
def keyStep : Dir → Instr
  | .encrypt => .alu .add kr (.imm 64)
  | .decrypt => .alu .sub kr (.imm 64)

/-- Four round keys, and on to the next four. -/
def prepGroup (d : Dir) : List Instr :=
  prepGroupX d ++ [.alu .add .eax (.imm 16), keyStep d, .alu .sub .ecx (.imm 1)]

/-- The table's address to the scratch buffer's first slot, the schedule
(the first stack argument), the keys' pointer, the eight groups, and the
mask. -/
def prepHead (d : Dir) : List Instr :=
  [.store (at_ sb 0) .eax, .mov tbr (.reg .eax), .mov .eax (.mem (argOp 0)), .mov kr (.reg sb),
   .alu .add kr (.imm (BitVec.ofNat 32 (keyBase d))), .mov .ecx (.imm 8), tb m0 oM0]

/-- The round keys the rounds read, in `d`'s order, from the schedule in
the first stack argument. -/
def prepare (d : Dir) : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block (prepHead d))
    (.loop (.block (prepGroup d)) .ne))

/-- The slots of the scratch buffer the core uses: the table's address,
seven spare slots, the ring's four places, the places of 33 round keys (the
last round reads the key after its own, which `prepare` does not write, and
does not use it), and the four blocks. -/
def slots : Nat := 172

/-- The modes' core: four blocks at a time, in the direction `d`. -/
def core (d : Dir) : Core :=
  { prepare := prepare d, crypt := crypt, slots := slots, total := slots + 10, buf := 156, G := 4, bw := 4,
    stack := 4, ka := 1 }

/-- The sizes of the groups of blocks a wide mode takes in turn, before the
blocks left one at a time. -/
def levels : List Nat := [4, 2]

/-- `vg_sm4_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa :=
  (core .decrypt).seqLevels (Modes.Mode.cbcDecWide 4) levels (Modes.Mode.cbcDecChained 4)

/-- `vg_sm4_cfb128_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa :=
  (core .encrypt).seqLevels (Modes.Mode.cfbDecWide 4) levels (Modes.Mode.cfbDecEarly 4)

/-- `vg_sm4_ctr`, with its scratch buffer as the fifth argument. -/
def ctr : Prog isa := (core .encrypt).seqLevels Modes.Mode.ctrWide levels Modes.Mode.ctrEarly

end VG.Impl.Sm4.X86.AesNiWide
