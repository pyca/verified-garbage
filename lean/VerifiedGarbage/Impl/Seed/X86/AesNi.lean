module

public import VerifiedGarbage.Impl.Modes.X86.Seq

/-!
# SEED on x86 (32-bit) with its S-boxes by `aesenclast`: one block

SEED's two S-boxes (RFC 4269 Appendix A.1) are the AES S-box between a
linear map of a byte, the same for both, and an affine map each
(`Proof/Seed/X86/AesNiMaps.lean`), so the S-boxes of a register are
`aesenclast` between byte maps, each two look-ups of a nibble with
`pshufb`. `aesenclast`'s round key is the mask `0x0f` of every byte, which
the code needs anyway: the low nibble arrives complemented, as the tables of
low nibbles after it expect.

A word fills a register: the same 32-bit value in each of the four lanes,
as `paddd` adds it (F joins its three G with additions, §2.1, so the words
stay as they are). `G` of the word in `xmm0` (§2.2), to `xmm0`: the map
before the S-box on the word's bytes; a shuffle that puts byte `l` of the
word in every byte of lane `l`, so that `aesenclast`'s ShiftRows leaves in
lane `c` the word's S-box inputs rotated by `c` bytes; `aesenclast`; both
maps after it, of every byte; two masks by position, which keep of each
byte the S-box of its place in the word and the `m` of the output byte it
is for; and the exclusive-or of the four lanes, which leaves `G`'s word in
every lane again.

`prepare` and `crypt` are a core of the modes (`core`,
`Impl.Modes.X86.Core`) for one block at a time. With the modes' scratch
buffer at `sb`: its first slot holds the address of the table of constants
`VG_SEED_AESNI` (taken once, by `prepare`, with `symPush`), the block is at
byte 8, four places of 16 bytes from byte 32 on hold the halves of the
state that wait for the next round, and from byte 96 on are the 32 round
keys, each in every lane of its 16 bytes, which `prepare` copies from the
schedule `vg_seed_expand_key` stores. A round has the right half `R0`,
`R1` in `xmm5` and `xmm0`: it stores them where the next round reads its
left half, adds its keys, read through `kr`, the pointer of the keys of its
turn, computes F, and adds the left half from where the round before left
it. Two rounds are a turn of the loop. Every store is at a fixed place of
the scratch buffer, through `sb`.

The code is `aes` and `ssse3` code: its dispatcher runs it only where the
CPU has both.
-/

@[expose] public section

namespace VG.Impl.Seed.X86.AesNi

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)

/-- The table of constants' name. -/
def tableName : String := "VG_SEED_AESNI"

/-- The constants, 16 bytes each (two words): the mask, the nibble tables
of the map before the S-box and of the two after it, the masks by position,
the shuffle before `aesenclast`, and the shuffle that reverses a lane's
bytes. -/
def table : List (BitVec 64) := [
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f, 0x42435b5a18190100, 0x2928303173726a6b,
  0xba4e768238ccf400, 0xbc4870843ecaf206, 0x572bf38f4c30e894, 0xe79b433ffc805824,
  0xc996a0ff36695f00, 0x431c2a75bce3d58a, 0xd6da9d91929ed9d5, 0x2b27606c6f632428,
  0x7a54507e042a2e00, 0x6846426c16383c12, 0x3f003f0000fc00fc, 0xf300f30000cf00cf,
  0x00f300f3cf00cf00, 0x003f003ffc00fc00, 0x0101010100000000, 0x0303030302020202,
  0x0405060700010203, 0x0c0d0e0f08090a0b
]

/-- The mask `0x0f` of every byte. -/
def oM0 : Nat := 0
/-- The map before the S-box: the tables of its low and its high nibble. -/
def oPRE : Nat := 16
/-- The map after it for `S0`: the tables of its low nibble (complemented)
and its high nibble. -/
def oP0 : Nat := 48
/-- For `S1`. -/
def oP1 : Nat := 80
/-- The masks by position: of `S0`'s bytes, and at `oKA + 16` of `S1`'s. -/
def oKA : Nat := 112
/-- Byte `l` of the first lane to every byte of lane `l`. -/
def oARR : Nat := 144
/-- A lane's bytes reversed. -/
def oBSW : Nat := 160

/-- The table's base register in `crypt`. -/
def tbr : Reg := .ebx
/-- The round keys' pointer: the keys of the turn at hand. -/
def kr : Reg := .esi
/-- The four places of the state's halves in the scratch buffer. -/
def oR : Nat := 32
/-- The mask `0x0f` of every byte. -/
def m0 : XReg := .xmm7

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def ld (d : XReg) (b : Reg) (off : Nat) : Instr := .movdquLoad d (at_ b off)
def stx (b : Reg) (off : Nat) (r : XReg) : Instr := .movdquStore (at_ b off) r

/-- `G`'s first part: the map before the S-box of the bytes of the word in
`xmm0`, byte `l` of the word in every byte of lane `l`, to `xmm2`. -/
def gPre : List Instr :=
  [x .movdqa .xmm1 .xmm0, .xop (.shift .psrld .xmm1 4), x .pand .xmm1 m0, x .pand .xmm0 m0,
   tb .xmm2 oPRE, x .pshufb .xmm2 .xmm0, tb .xmm3 (oPRE + 16), x .pshufb .xmm3 .xmm1, x .pxor .xmm2 .xmm3,
   tb .xmm3 oARR, x .pshufb .xmm2 .xmm3]

/-- `G`'s second part: the S-boxes of `xmm2`, the maps after them, the masks
by position, and the four lanes together, to `xmm0`. -/
def gPost : List Instr :=
  [x .aesenclast .xmm2 m0,
   x .movdqa .xmm1 .xmm2, .xop (.shift .psrld .xmm1 4), x .pand .xmm1 m0, x .pand .xmm2 m0,
   tb .xmm0 oP0, x .pshufb .xmm0 .xmm2, tb .xmm3 (oP0 + 16), x .pshufb .xmm3 .xmm1, x .pxor .xmm0 .xmm3,
   tb .xmm4 oP1, x .pshufb .xmm4 .xmm2, tb .xmm3 (oP1 + 16), x .pshufb .xmm3 .xmm1, x .pxor .xmm4 .xmm3,
   tb .xmm3 oKA, x .pand .xmm0 .xmm3, tb .xmm3 (oKA + 16), x .pand .xmm4 .xmm3, x .pxor .xmm0 .xmm4,
   .xop (.pshufd .xmm1 .xmm0 0x39), .xop (.pshufd .xmm2 .xmm0 0x4e), .xop (.pshufd .xmm3 .xmm0 0x93),
   x .pxor .xmm0 .xmm1, x .pxor .xmm2 .xmm3, x .pxor .xmm0 .xmm2]

/-- `xmm0 = G(xmm0)`; `xmm1` to `xmm4` are lost, `xmm5` and `xmm6` kept. -/
def g : List Instr := gPre ++ gPost

/-- F (§2.1) of `A = R0 ⊕ Ki0` in `xmm5` and `B = R1 ⊕ Ki1` in `xmm0`: its
first word to `xmm5` and its second to `xmm0`. -/
def fX : List Instr :=
  x .pxor .xmm0 .xmm5 :: (g ++ (x .movdqa .xmm6 .xmm0 :: x .paddd .xmm0 .xmm5 :: (g ++
    (x .movdqa .xmm5 .xmm0 :: x .paddd .xmm0 .xmm6 :: (g ++ [x .paddd .xmm5 .xmm0])))))

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

/-- The mask, and the block in `xmm0` to its four words: `L0` and `L1` to
the first two places, `R0` to `xmm5` and `R1` to `xmm0`. -/
def headX : List Instr :=
  [tb m0 oM0, tb .xmm4 oBSW, x .pshufb .xmm0 .xmm4,
   .xop (.pshufd .xmm1 .xmm0 0x00), stx sb oR .xmm1, .xop (.pshufd .xmm1 .xmm0 0x55), stx sb (oR + 16) .xmm1,
   .xop (.pshufd .xmm5 .xmm0 0xaa), .xop (.pshufd .xmm0 .xmm0 0xff)]

/-- The table's address, the keys' pointer, the eight turns, and the block
at byte 8 of the scratch buffer to its words. -/
def cryptHead : List Instr :=
  [.mov tbr (.mem (at_ sb 0)), .mov kr (.reg sb), .alu .add kr (.imm 96), .mov .eax (.imm 8), ld .xmm0 sb 8] ++ headX

/-- The last right half, in `xmm5` and `xmm0`, then the last left half,
from the first two places, to the block's bytes, in `xmm5`. -/
def tailX : List Instr :=
  [x .punpcklqdq .xmm5 .xmm0, .xop (.pshufd .xmm5 .xmm5 0x88),
   ld .xmm1 sb oR, ld .xmm2 sb (oR + 16), x .punpcklqdq .xmm1 .xmm2, .xop (.pshufd .xmm1 .xmm1 0x88),
   x .punpcklqdq .xmm5 .xmm1, tb .xmm4 oBSW, x .pshufb .xmm5 .xmm4]

/-- The last words to the block. -/
def cryptTail : List Instr := tailX ++ [stx sb 8 .xmm5]

/-- The block of the core's buffer, enciphered in place. -/
def crypt : Prog isa :=
  .seq (.block cryptHead) (.seq (.loop (.block turn) .ne) (.block cryptTail))

/-- Four round keys of the schedule (at `eax`), each to every lane of its
place at `kr`. -/
def prepGroupX : List Instr :=
  [ld .xmm0 .eax 0,
   .xop (.pshufd .xmm4 .xmm0 0x00), stx kr 0 .xmm4, .xop (.pshufd .xmm4 .xmm0 0x55), stx kr 16 .xmm4,
   .xop (.pshufd .xmm4 .xmm0 0xaa), stx kr 32 .xmm4, .xop (.pshufd .xmm4 .xmm0 0xff), stx kr 48 .xmm4]

/-- Four round keys, and on to the next four. -/
def prepGroup : List Instr :=
  prepGroupX ++ [.alu .add .eax (.imm 16), .alu .add kr (.imm 64), .alu .sub .ecx (.imm 1)]

/-- The table's address to the scratch buffer's first slot and to its
register, the schedule (the first stack argument), the keys' pointer, and
the eight groups. -/
def prepHead : List Instr :=
  [.store (at_ sb 0) .eax, .mov tbr (.reg .eax), .mov .eax (.mem (argOp 0)), .mov kr (.reg sb),
   .alu .add kr (.imm 96), .mov .ecx (.imm 8)]

/-- The round keys the rounds read, from the schedule in the first stack
argument. -/
def prepare : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block prepHead)
    (.loop (.block prepGroup) .ne))

/-- The slots of the scratch buffer the core uses: the table's address and
a spare slot, the block, two spare slots, the four places of the state's
halves, and the places of the 32 round keys. -/
def slots : Nat := 152

/-- The modes' core: one block at a time. -/
def core : Core :=
  { prepare := prepare, crypt := crypt, slots := slots, total := slots + 10, buf := 2, G := 1, bw := 4,
    stack := 4, ka := 1 }

end VG.Impl.Seed.X86.AesNi
