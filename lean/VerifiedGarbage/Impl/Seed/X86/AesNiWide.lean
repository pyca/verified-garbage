module

public import VerifiedGarbage.Impl.Seed.X86.AesNi
public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Spec.Seed

/-!
# SEED on x86 (32-bit) with its S-boxes by `aesenclast`: four blocks

The one-block code (`Impl/Seed/X86/AesNi.lean`) on four blocks at once: a
register holds one word of four blocks, block `l`'s in the 32-bit lane `l`,
as `paddd` adds it, so F's three additions and its exclusive-ors are the
one-block code's. `G` of the words in `xmm0`, to `xmm0`: the map before the
S-box of every byte; `aesenclast`, whose ShiftRows moves the bytes between
the lanes; the map after it for `S0` of every byte, and the difference of
the two maps after it of every byte, masked to the bytes at the odd places
of a word, where `S1` is; then, for `r` from 0 to 3, the bytes under their
masks `m` for the output byte `r` places before them (the mask by position
at `oKB + 16 r`), brought back to their lanes `r` bytes down by one shuffle
(the inverse of ShiftRows, then the rotation of each lane's bytes, at
`oRC + 16 r`), and the four together.

No register on the way from a `G`'s input to its output is written whole
with anything but a constant: the low nibbles are a copy of the mask, then
the bytes under it; each look-up's row and each mask by position is loaded
into the register that then takes the data; the shuffles' rows go through
`xmm3`, which holds nothing else; and of F's three words between its `G`s
one waits in the scratch buffer (at `oC`). On processors on which such a
write waits for the register's old value while the AVX registers' upper
halves are not zero, the code then runs as it does elsewhere.

`prepare d` and `crypt` are a core of the modes (`core d`,
`Impl.Modes.X86.Core`) for four blocks at a time, in the direction `d`.
With the modes' scratch buffer at `sb`: its first slot holds the address
of the table of constants `VG_SEED_AESNI_WIDE`; five places of 16 bytes
from byte 16 on hold the halves of the state that wait for the next round
and F's word; from byte 96 on are the 32 round keys, each in every lane of
its 16 bytes, in the order the rounds read them, which `prepare d` copies
from the schedule `vg_seed_expand_key` stores: for decryption the rounds'
keys in reverse order (RFC 4269 §2.4), so that both directions run the same
rounds; and the four blocks are at byte 608. `crypt` reverses the bytes of
each block's words and transposes the 4 × 4 doublewords, so that a register
holds a word of the four blocks, runs the one-block code's sixteen rounds,
and transposes back. Every store is at a fixed place of the scratch buffer,
through `sb`.

CBC and CFB128 decryption, whose blocks can be deciphered independently,
take the blocks in groups (`Impl/Modes/X86/Wide.lean`): of four while four
are left, then of two (`levels`), then one, each group one pass of `crypt`
over the buffer.

The code is `aes` and `ssse3` code: its dispatcher runs it only where the
CPU has both.
-/

@[expose] public section

namespace VG.Impl.Seed.X86.AesNiWide

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)
open VG.Impl.Seed.X86.AesNi (x ld stx tbr kr m0)
open VG.Spec.Seed (Direction)

/-- The table of constants' name. -/
def tableName : String := "VG_SEED_AESNI_WIDE"

/-- The constants, 16 bytes each (two words): the mask, the nibble tables
of the map before the S-box, of the map after it for `S0` and of the
difference of the two maps after it, the mask of the odd places, the four
masks by position, the four shuffles that bring the bytes back to their
lanes, rotated, and the shuffle that reverses a lane's bytes. -/
def table : List (BitVec 64) := [
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f, 0x42435b5a18190100, 0x2928303173726a6b,
  0xba4e768238ccf400, 0xbc4870843ecaf206, 0x572bf38f4c30e894, 0xe79b433ffc805824,
  0xc996a0ff36695f00, 0x431c2a75bce3d58a, 0x81f16e1edeae3141, 0xccbc235393e37c0c,
  0xb3c2f08132437100, 0x2b5a6819aadbe998, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00,
  0xcffccffccffccffc, 0xcffccffccffccffc, 0xf33ff33ff33ff33f, 0xf33ff33ff33ff33f,
  0xfccffccffccffccf, 0xfccffccffccffccf, 0x3ff33ff33ff33ff3, 0x3ff33ff33ff33ff3,
  0x0b0e0104070a0d00, 0x0306090c0f020508, 0x040b0e0100070a0d, 0x0c030609080f0205,
  0x01040b0e0d00070a, 0x090c030605080f02, 0x0e01040b0a0d0007, 0x06090c030205080f,
  0x0405060700010203, 0x0c0d0e0f08090a0b
]

/-- The mask `0x0f` of every byte. -/
def oM0 : Nat := 0
/-- The map before the S-box: the tables of its low and its high nibble. -/
def oPRE : Nat := 16
/-- The map after it for `S0`: the tables of its low nibble (complemented)
and its high nibble. -/
def oP0 : Nat := 48
/-- The difference of the maps after it for `S0` and for `S1`. -/
def oD : Nat := 80
/-- The mask of the odd places of a word. -/
def oE1 : Nat := 112
/-- The masks by position: at `oKB + 16 r`, of a byte for the output byte
`r` places before it in its word. -/
def oKB : Nat := 128
/-- The shuffles: at `oRC + 16 r`, the inverse of ShiftRows, then each
lane's bytes `r` places down. -/
def oRC : Nat := 192
/-- A lane's bytes reversed. -/
def oBSW : Nat := 256

/-- The places of the state's halves in the scratch buffer, and F's word's. -/
def oR : Nat := 16
def oC : Nat := 80
/-- The four blocks in the scratch buffer. -/
def oB : Nat := 608

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table

/-- `G`'s first part: the map before the S-box of the bytes of `xmm0`, to
`xmm1`. -/
def gPre : List Instr :=
  [x .movdqa .xmm2 m0, x .pand .xmm2 .xmm0, .xop (.shift .psrld .xmm0 4), x .pand .xmm0 m0,
   tb .xmm1 oPRE, x .pshufb .xmm1 .xmm2, tb .xmm4 (oPRE + 16), x .pshufb .xmm4 .xmm0, x .pxor .xmm1 .xmm4]

/-- The bytes of `xmm0` under their masks for the output byte `r` places
before them, in their lanes `r` bytes down, to `t`. -/
def spread (r : Nat) (t : XReg) : List Instr :=
  [tb t (oKB + 16 * r), x .pand t .xmm0, tb .xmm3 (oRC + 16 * r), x .pshufb t .xmm3]

/-- `G`'s second part: the S-boxes of `xmm1`, the maps after them, and the
spread of each byte over its word, to `xmm0`. -/
def gPost : List Instr :=
  [x .aesenclast .xmm1 m0,
   x .movdqa .xmm2 m0, x .pand .xmm2 .xmm1, .xop (.shift .psrld .xmm1 4), x .pand .xmm1 m0,
   tb .xmm0 oP0, x .pshufb .xmm0 .xmm2, tb .xmm4 oD, x .pshufb .xmm4 .xmm2,
   tb .xmm6 (oP0 + 16), x .pshufb .xmm6 .xmm1, tb .xmm2 (oD + 16), x .pshufb .xmm2 .xmm1,
   x .pxor .xmm0 .xmm6, x .pxor .xmm4 .xmm2, tb .xmm3 oE1, x .pand .xmm4 .xmm3, x .pxor .xmm0 .xmm4] ++
  spread 1 .xmm1 ++ spread 2 .xmm2 ++ spread 3 .xmm6 ++
  [tb .xmm3 oKB, x .pand .xmm0 .xmm3, tb .xmm3 oRC, x .pshufb .xmm0 .xmm3,
   x .pxor .xmm0 .xmm1, x .pxor .xmm2 .xmm6, x .pxor .xmm0 .xmm2]

/-- `xmm0 = G(xmm0)` in every lane; `xmm1` to `xmm4` and `xmm6` are lost,
`xmm5` kept. -/
def g : List Instr := gPre ++ gPost

/-- F (§2.1) of `A = R0 ⊕ Ki0` in `xmm5` and `B = R1 ⊕ Ki1` in `xmm0`: its
first word to `xmm5` and its second to `xmm0`; `C` waits at `oC`. -/
def fX : List Instr :=
  x .pxor .xmm0 .xmm5 :: (g ++ (stx sb oC .xmm0 :: x .paddd .xmm0 .xmm5 :: (g ++
    (x .movdqa .xmm5 .xmm0 :: ld .xmm1 sb oC :: x .paddd .xmm0 .xmm1 :: (g ++ [x .paddd .xmm5 .xmm0])))))

/-- Round `h` of a turn (0 or 1), its start: the right half to the places
`2 - 2 h` and `3 - 2 h`, where the next round reads its left half, and the
round's keys, at `kr + 32 h`, added to it. -/
def keyX (h : Nat) : List Instr :=
  [stx sb (oR + 16 * (2 - 2 * h)) .xmm5, stx sb (oR + 16 * (3 - 2 * h)) .xmm0,
   ld .xmm1 kr (32 * h), x .pxor .xmm5 .xmm1, ld .xmm1 kr (32 * h + 16), x .pxor .xmm0 .xmm1]

/-- Its end: the left half, from the places `2 h` and `2 h + 1`, added to F. -/
def leftX (h : Nat) : List Instr :=
  [ld .xmm1 sb (oR + 32 * h), x .pxor .xmm5 .xmm1, ld .xmm1 sb (oR + 32 * h + 16), x .pxor .xmm0 .xmm1]

/-- Round `h` of a turn: from the right half in `xmm5` and `xmm0` to the
next round's. -/
def round (h : Nat) : List Instr := keyX h ++ (fX ++ leftX h)

/-- On by four keys; a turn fewer. -/
def step : List Instr := [.alu .add kr (.imm 64), .alu .sub .eax (.imm 1)]

/-- A turn of the loop: two rounds. -/
def turn : List Instr := round 0 ++ (round 1 ++ step)

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

/-- Block `j` of the buffer, the bytes of each of its words reversed, to `r`. -/
def blockIn (j : Nat) (r : XReg) : List Instr := [ld r sb (oB + 16 * j), x .pshufb r .xmm4]

/-- The mask, and the four blocks to their four words, in `xmm0`, `xmm3`,
`xmm4` and `xmm1`. -/
def headX : List Instr :=
  [tb m0 oM0, tb .xmm4 oBSW] ++ blockIn 0 .xmm0 ++ blockIn 1 .xmm1 ++ blockIn 2 .xmm2 ++ blockIn 3 .xmm3 ++
    transpose

/-- `L0` and `L1` to the first two places, `R0` to `xmm5` and `R1` to
`xmm0`. -/
def headS : List Instr :=
  [stx sb oR .xmm0, stx sb (oR + 16) .xmm3, x .movdqa .xmm5 .xmm4, x .movdqa .xmm0 .xmm1]

/-- The table's address, the keys' pointer and the eight turns. -/
def cryptRegs : List Instr :=
  [.mov tbr (.mem (at_ sb 0)), .mov kr (.reg sb), .alu .add kr (.imm 96), .mov .eax (.imm 8)]

/-- The buffer's four blocks to their words, and the registers of the loop. -/
def cryptHead : List Instr := cryptRegs ++ headX ++ headS

/-- The last right half, in `xmm5` and `xmm0`, then the last left half,
from the first two places, to the four blocks' bytes: in `xmm0`, `xmm3`,
`xmm4` and `xmm1`. -/
def tailX : List Instr :=
  [x .movdqa .xmm1 .xmm0, x .movdqa .xmm0 .xmm5, ld .xmm2 sb oR, ld .xmm3 sb (oR + 16)] ++ transpose ++
    [tb .xmm2 oBSW, x .pshufb .xmm0 .xmm2, x .pshufb .xmm3 .xmm2, x .pshufb .xmm4 .xmm2, x .pshufb .xmm1 .xmm2]

/-- Four registers to four places of 16 bytes of the scratch buffer, from
byte `o` on. -/
def stores (o : Nat) (r0 r1 r2 r3 : XReg) : List Instr :=
  [stx sb o r0, stx sb (o + 16) r1, stx sb (o + 32) r2, stx sb (o + 48) r3]

/-- The last words to the buffer's four blocks. -/
def cryptTail : List Instr := tailX ++ stores oB .xmm0 .xmm3 .xmm4 .xmm1

/-- The four blocks of the core's buffer, enciphered in place. -/
def crypt : Prog isa :=
  .seq (.block cryptHead) (.seq (.loop (.block turn) .ne) (.block cryptTail))

/-- Where the keys' pointer starts in `prepare`: the first four places, or,
for decryption, the last four. -/
def keyBase : Direction → Nat
  | .encrypt => 96
  | .decrypt => 544

/-- The lane of the group's four keys (two rounds') that goes to the place
at `kr + 16 w`: the keys in their order, or, for decryption, the later
round's first. -/
def keyLane : Direction → Nat → BitVec 8
  | .encrypt, w => BitVec.ofNat 8 (0x55 * w)
  | .decrypt, w => BitVec.ofNat 8 (0x55 * ((w + 2) % 4))

/-- Four round keys of the schedule (at `eax`), each to every lane of its
place at `kr`. -/
def prepGroupX (d : Direction) : List Instr :=
  [ld .xmm0 .eax 0,
   .xop (.pshufd .xmm4 .xmm0 (keyLane d 0)), stx kr 0 .xmm4, .xop (.pshufd .xmm4 .xmm0 (keyLane d 1)), stx kr 16 .xmm4,
   .xop (.pshufd .xmm4 .xmm0 (keyLane d 2)), stx kr 32 .xmm4, .xop (.pshufd .xmm4 .xmm0 (keyLane d 3)), stx kr 48 .xmm4]

/-- The keys' pointer to the next four places. -/
def keyStep : Direction → Instr
  | .encrypt => .alu .add kr (.imm 64)
  | .decrypt => .alu .sub kr (.imm 64)

/-- Four round keys, and on to the next four. -/
def prepGroup (d : Direction) : List Instr :=
  prepGroupX d ++ [.alu .add .eax (.imm 16), keyStep d, .alu .sub .ecx (.imm 1)]

/-- The table's address to the scratch buffer's first slot, the schedule
(the first stack argument), the keys' pointer, and the eight groups. -/
def prepHead (d : Direction) : List Instr :=
  [.store (at_ sb 0) .eax, .mov tbr (.reg .eax), .mov .eax (.mem (argOp 0)), .mov kr (.reg sb),
   .alu .add kr (.imm (BitVec.ofNat 32 (keyBase d))), .mov .ecx (.imm 8)]

/-- The round keys the rounds read, in `d`'s order, from the schedule in
the first stack argument. -/
def prepare (d : Direction) : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block (prepHead d))
    (.loop (.block (prepGroup d)) .ne))

/-- The slots of the scratch buffer the core uses: the table's address and
three spare slots, the five places, the places of the 32 round keys, and the
four blocks. -/
def slots : Nat := 168

/-- The modes' core: four blocks at a time, in the direction `d`. -/
def core (d : Direction) : Core :=
  { prepare := prepare d, crypt := crypt, slots := slots, total := slots + 10, buf := 152, G := 4, bw := 4,
    stack := 4, ka := 1 }

/-- The sizes of the groups of blocks a wide mode takes in turn, before the
blocks left one at a time. -/
def levels : List Nat := [4, 2]

/-- `vg_seed_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa :=
  (core .decrypt).seqLevels (Modes.Mode.cbcDecWide 4) levels (Modes.Mode.cbcDecChained 4)

/-- `vg_seed_cfb128_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa :=
  (core .encrypt).seqLevels (Modes.Mode.cfbDecWide 4) levels (Modes.Mode.cfbDecEarly 4)

end VG.Impl.Seed.X86.AesNiWide
