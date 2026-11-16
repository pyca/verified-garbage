module

public import VerifiedGarbage.Impl.Aes.AArch64.Sbox

/-!
# The linear layers of bitsliced AES on AArch64

The state of four blocks is eight 64-bit words in `q 0 … q 7`, word `j`
holding bit `j` of the 64 bytes: byte `i = r + 4c` (row `r`, column `c`)
of block `b` is at bit position `16r + 4c + b`, as in BearSSL's
`aes_ct64` (Thomas Pornin, MIT licence), whose `ortho`, `interleave_in`,
`shift_rows` and `mix_columns` these follow. So ShiftRows rotates each
16-bit row, and MixColumns rotates whole words by 16 and 32 bits.

Every block here uses the state registers, the mask registers `m 1 … m 6`
(built with `movz` and `movk`) and the temporaries `t0`, `t1`, `u7` and
`t2`; AddRoundKey loads the round key from `kp`. None uses memory otherwise.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- The registers of the masks. -/
def m : Nat → Reg
  | 1 => .x14 | 2 => .x15 | 3 => .x16 | 4 => .x17 | 5 => .x19 | _ => .x20

/-- The temporaries. -/
def t0 : Reg := .x21
def t1 : Reg := .x22
def u7 : Reg := .x23
def t2 : Reg := .x24

def rorI (d n : Reg) (sh : Nat) : Instr := .ror .x d n sh
def lsrI (d n : Reg) (sh : Nat) : Instr := .lsr .x d n sh

/-- The halfword `k` of `v`. -/
def half (v : BitVec 64) (k : Nat) : BitVec 16 := v.extractLsb' (16 * k) 16

/-- `d := v`: `movz` of its lowest halfword, then `movk` of the others that are not zero. -/
def imm (d : Reg) (v : BitVec 64) : List Instr :=
  .movz .x d (half v 0) 0 :: ([1, 2, 3].filter (half v · != 0)).map fun k => .movk .x d (half v k) k

/-! ## Between bytes and the bitsliced state -/

/-- A delta swap within `x`: exchanges the bits of `x` in the mask `mk`
with the bits `s` places above them (`t` is clobbered). -/
def swapIn (x t mk : Reg) (s : Nat) : List Instr :=
  [lsrI t x s, eorR t t x, andR t t mk, eorR x x t, rorI t t (64 - s), eorR x x t]

/-- A delta swap between `x` and `y` (BearSSL's `SWAPN`): exchanges the bits
of `y` in the mask `mk` with the bits of `x` `s` places above them. -/
def swapBetween (x y t mk : Reg) (s : Nat) : List Instr :=
  [lsrI t x s, eorR t t y, andR t t mk, eorR y y t, rorI t t (64 - s), eorR x x t]

/-- The masks of the transposes. -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00), (3, 0x00FF00FF00FF00FF),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

def setMasks (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => imm (m k) v

/-- Bytes `0 1 2 3 4 5 6 7` of each word become `0 4 1 5 2 6 3 7`. -/
def zip1 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) t0 (m 1) 16
def zip2 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) t0 (m 2) 8

/-- Interleave the bytes of `q b` and `q (b + 4)`. -/
def swap8 : List Instr := (List.range 4).flatMap fun b => swapBetween (q b) (q (b + 4)) t0 (m 3) 8

/-- BearSSL's `br_aes_ct64_ortho`: transposes the 8×8 bit matrix in each
byte position of the eight words. -/
def ortho : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 (m 4) 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 (m 5) 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) t0 (m 6) 4)

/-! ## The round transformations -/

/-- The register pointing to the round key. -/
def kp : Reg := .x1

end VG.Impl.Aes.AArch64
