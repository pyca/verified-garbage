module

public import VerifiedGarbage.Impl.Modes.X86.Seq

/-!
# SM4 on x86 (32-bit) with its S-box by `aesenclast`: one block

SM4's S-box is the AES S-box between two affine maps of a byte (GB/T
32907-2016 §6.2; `Proof/Sm4/X86/AesNiMaps.lean`), so a register's S-boxes
are `aesenclast` between byte maps, each two look-ups of a nibble with
`pshufb`. `aesenclast`'s round key is the mask `0x0f` of every byte, which
the code needs anyway: the low nibble arrives complemented, as the tables of
low nibbles after it expect.

A word fills a register: its four bytes, in the block's order (the most
significant first), in each of the four 32-bit lanes, so that
`aesenclast`'s ShiftRows only moves a byte to the same byte of another
lane. Every word `X` is kept as `PL X`, the linear part of the map before
the S-box on each byte, so that nothing is between a round's exclusive-or
and its `aesenclast`: with the round keys as `PK rk` (`PL rk` and the map's
constant), `aesenclast` takes `PL X₁ ⊕ PL X₂ ⊕ PL X₃ ⊕ PK rk`. What follows
it is `PL ∘ L ∘` (the map after the S-box): `L(B)`'s byte `j` is
`M0 b[j] ⊕ M1 b[j+1] ⊕ M1 b[j+2] ⊕ M3 b[j+3]` for three linear maps of a
byte with `M0 = M1 ⊕ M3`, so a round adds `E ⊕ H ⊕ rot¹ E ⊕ rot² E ⊕ rot³ H`
for two byte maps `E` and `H` of `aesenclast`'s output (four look-ups) and
rotations of a word by bytes (three shuffles).

`prepare` and `crypt` are a core of the modes (`core`,
`Impl.Modes.X86.Core`) for one block at a time. With the modes' scratch
buffer at `sb`: its first slot holds the address of the table of constants
`VG_SM4_AESNI` (taken once, by `prepare`, with `symPush`), the block is at
byte 8, and from byte 32 on are 36 entries of 32 bytes: entry `i` holds
`PK rkᵢ` (`prepare` makes the 32 from the schedule `vg_sm4_expand_key`
stores), then `PL Xᵢ`, the block's words `X₀ … X₃` and the 32 that the
rounds add, each stored as it is made. A round reads its words and the next
round's key through `kr`, the pointer of its entry, and stores its word
through `kw`; it has `aesenclast`'s input and the newest word in two
registers, and leaves the next round's in two others, so that no register
is copied on the way from one `aesenclast` to the next: two rounds are a
turn of the loop.

The code is `aes` and `ssse3` code: its dispatcher runs it only where the
CPU has both.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86.AesNi

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp Core)

/-- The table of constants' name. -/
def tableName : String := "VG_SM4_AESNI"

/-- The constants, 16 bytes each (two words): the mask, the nibble tables
of the byte maps, the rotations of a word by bytes, and the shuffle that
reverses a lane's bytes. -/
def table : List (BitVec 64) := [
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f, 0x25d5e81854a49969, 0xb9497484c83805f5,
  0xdc4be572ae399700, 0xec7bd5429e09a730, 0x1c44643cbce4c49c, 0x00587820a0f8d880,
  0xe897067991ee7f00, 0xa4db4a35dda2334c, 0x0407060500030201, 0x0c0f0e0d080b0a09,
  0x0504070601000302, 0x0d0c0f0e09080b0a, 0x0605040702010003, 0x0e0d0c0f0a09080b,
  0x9096e3e575730600, 0xc6c0b5b323255056, 0xe240ab09eb49a200, 0xf052b91bf95bb012,
  0x74019de89ce97500, 0x4134a8dda9dc4035, 0x9ef70960fe976900, 0xf099670e90f9076e,
  0x9197e2e474720701, 0xc7c1b4b222245157, 0xe240ab09eb49a200, 0xf052b91bf95bb012,
  0x0405060700010203, 0x0c0d0e0f08090a0b
]

/-- The mask `0x0f` of every byte. -/
def oM0 : Nat := 0
/-- `E`: the tables of its low nibble (complemented) and its high nibble. -/
def oE : Nat := 16
/-- `H`. -/
def oH : Nat := 48
/-- The rotation of every lane by `k` bytes is at `oBR + 16 (k - 1)`. -/
def oBR : Nat := 80
/-- `PL`, into the rounds' form. -/
def oCV : Nat := 128
/-- Out of it. -/
def oIV : Nat := 160
/-- `PK`: `PL` and the constant of the map before the S-box. -/
def oK : Nat := 192
/-- A lane's bytes reversed. -/
def oBSW : Nat := 224

/-- The table's base register in `prepare` and `crypt`. -/
def tbr : Reg := .ebx
/-- The entries' pointer: the entry of the round at hand. -/
def kr : Reg := .esi
/-- Where a round's new word goes: the fifth entry's from `kr`. -/
def kw : Reg := .ecx
/-- The mask `0x0f` of every byte, in both. -/
def m0 : XReg := .xmm7

/-- A constant to `d`. -/
def tb (d : XReg) (off : Nat) : Instr := .movdquTbl d (at_ tbr off) tableName table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)
def ld (d : XReg) (b : Reg) (off : Nat) : Instr := .movdquLoad d (at_ b off)
def stx (b : Reg) (off : Nat) (r : XReg) : Instr := .movdquStore (at_ b off) r

/-- The byte map at `t` (`oCV`, `oIV` or `oK`) of every byte of `v`, to
`b`; `v`, `a` and `c` are lost. -/
def conv (v a b c : XReg) (t : Nat) : List Instr :=
  [x .movdqa a v, .xop (.shift .psrld a 4), x .pand a m0, x .pand v m0,
   tb b t, x .pshufb b v, tb c (t + 16), x .pshufb c a, x .pxor b c]

/-- Round `r` of a turn (0 or 1), of the entry at `kr + 32 r`:
`aesenclast`'s input is in `a` and the newest word in `n`; the next
round's are left in `c` and `e`, and the new word in the fifth entry from
this one, at `kw + 32 r`. `e` first holds the next round's key and the two
words it has of that round's three; `xmm3` this round's word and them, then
the round's sum. -/
def round (a c n e : XReg) (r : Nat) : List Instr :=
  [ld e kr (32 * r + 32), ld .xmm6 kr (32 * r + 80), x .pxor e .xmm6, x .pxor e n,
   ld .xmm3 kr (32 * r + 16), x .pxor .xmm3 e,
   x .aesenclast a m0,
   x .movdqa n a, x .pand n m0, .xop (.shift .psrld a 4), x .pand a m0,
   tb c oE, x .pshufb c n, tb .xmm5 oH, x .pshufb .xmm5 n, x .movdqa n c,
   tb .xmm6 (oE + 16), x .pshufb .xmm6 a, x .pxor c .xmm6, x .pxor n .xmm6,
   tb .xmm6 (oH + 16), x .pshufb .xmm6 a, x .pxor .xmm5 .xmm6,
   x .pxor .xmm3 c, x .pxor .xmm3 .xmm5,
   tb .xmm6 oBR, x .pshufb c .xmm6, tb a (oBR + 16), x .pshufb n a, x .pxor c n,
   tb .xmm6 (oBR + 32), x .pshufb .xmm5 .xmm6, x .pxor .xmm3 .xmm5,
   x .pxor c .xmm3,
   x .pxor e c, stx kw (32 * r) e]

/-- A turn's first round: from `xmm0` and `xmm1` to `xmm4` and `xmm2`. -/
def roundA : List Instr := round .xmm0 .xmm4 .xmm1 .xmm2 0
/-- Its second: back to `xmm0` and `xmm1`. -/
def roundB : List Instr := round .xmm4 .xmm0 .xmm2 .xmm1 1

/-- On by two entries; a turn fewer. -/
def step : List Instr := [.alu .add kr (.imm 64), .alu .add kw (.imm 64), .alu .sub .eax (.imm 1)]

/-- A turn of the loop: two rounds. -/
def turn : List Instr := roundA ++ roundB ++ step

/-- The block in `xmm0` to its four words in the rounds' form, in the first
four entries; the last of them left in `xmm1`, and the exclusive-or of the
last three in `xmm0`. -/
def headX : List Instr :=
  [tb m0 oM0] ++ conv .xmm0 .xmm1 .xmm2 .xmm3 oCV ++
    [.xop (.pshufd .xmm3 .xmm2 0x00), stx kr 16 .xmm3, .xop (.pshufd .xmm0 .xmm2 0x55), stx kr 48 .xmm0,
     .xop (.pshufd .xmm3 .xmm2 0xaa), stx kr 80 .xmm3, .xop (.pshufd .xmm1 .xmm2 0xff), stx kr 112 .xmm1,
     x .pxor .xmm0 .xmm3, x .pxor .xmm0 .xmm1]

/-- The table's address, the entries' pointer, the pointer of the words'
places, the 16 turns, and the block at byte 8 of the scratch buffer to the
first four entries. -/
def cryptHead : List Instr :=
  [.mov tbr (.mem (at_ sb 0)), .mov kr (.reg sb), .alu .add kr (.imm 32), .mov kw (.reg kr),
   .alu .add kw (.imm 144), .mov .eax (.imm 16), ld .xmm0 sb 8] ++ headX

/-- The first round's key. -/
def cryptKey : List Instr := [ld .xmm3 kr 0, x .pxor .xmm0 .xmm3]

/-- The last four words (the entries at `kr`), the last first, to the
block's bytes, in `xmm2`. -/
def tailX : List Instr :=
  [ld .xmm0 kr 112, ld .xmm1 kr 80, x .punpcklqdq .xmm0 .xmm1, .xop (.pshufd .xmm0 .xmm0 0x88),
   ld .xmm1 kr 48, ld .xmm2 kr 16, x .punpcklqdq .xmm1 .xmm2, .xop (.pshufd .xmm1 .xmm1 0x88),
   x .punpcklqdq .xmm0 .xmm1] ++
    conv .xmm0 .xmm1 .xmm2 .xmm3 oIV

/-- The last four words to the block. -/
def cryptTail : List Instr := tailX ++ [stx sb 8 .xmm2]

/-- The block of the core's buffer, enciphered in place. -/
def crypt : Prog isa :=
  .seq (.block (cryptHead ++ cryptKey)) (.seq (.loop (.block turn) .ne) (.block cryptTail))

/-- Four round keys of the schedule (at `eax`), in the rounds' form, to the
entries at `kr`. -/
def prepGroupX : List Instr :=
  [ld .xmm0 .eax 0, tb .xmm1 oBSW, x .pshufb .xmm0 .xmm1] ++ conv .xmm0 .xmm1 .xmm2 .xmm3 oK ++
    [.xop (.pshufd .xmm3 .xmm2 0x00), stx kr 0 .xmm3, .xop (.pshufd .xmm3 .xmm2 0x55), stx kr 32 .xmm3,
     .xop (.pshufd .xmm3 .xmm2 0xaa), stx kr 64 .xmm3, .xop (.pshufd .xmm3 .xmm2 0xff), stx kr 96 .xmm3]

/-- Four round keys, and on to the next four. -/
def prepGroup : List Instr :=
  prepGroupX ++ [.alu .add .eax (.imm 16), .alu .add kr (.imm 128), .alu .sub .ecx (.imm 1)]

/-- The table's address to the scratch buffer's first slot, the schedule
(the first stack argument), the entries' pointer, the eight groups, and the
mask. -/
def prepHead : List Instr :=
  [.store (at_ sb 0) .eax, .mov tbr (.reg .eax), .mov .eax (.mem (argOp 0)), .mov kr (.reg sb),
   .alu .add kr (.imm 32), .mov .ecx (.imm 8), tb m0 oM0]

/-- The round keys the rounds read, from the schedule in the first stack
argument. -/
def prepare : Prog isa :=
  .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block prepHead)
    (.loop (.block prepGroup) .ne))

/-- The slots of the scratch buffer the core uses: the table's address and
a spare slot, the block, two spare slots, and the 36 entries. -/
def slots : Nat := 296

/-- The modes' core: one block at a time. -/
def core : Core :=
  { prepare := prepare, crypt := crypt, slots := slots, total := slots + 10, buf := 2, G := 1, bw := 4,
    stack := 4, ka := 1 }

end VG.Impl.Sm4.X86.AesNi
