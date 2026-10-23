module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Sbox

/-!
# The linear layers of bitsliced AES on PPC64LE

The state of four blocks is eight 64-bit words in `q 0 … q 7`, word `j`
holding bit `j` of the 64 bytes: byte `i = r + 4c` (row `r`, column `c`)
of block `b` is at bit position `16r + 4c + b`, as in BearSSL's
`aes_ct64` (Thomas Pornin, MIT licence), whose `ortho`, `interleave_in`,
`shift_rows` and `mix_columns` these follow, as the x86-64 code does
(`Impl/Aes/X86_64/Linear.lean`). So ShiftRows rotates each 16-bit row, and
MixColumns rotates whole words by 16 and 32 bits.

The masks are built in registers (`m 1 … m 6`) by each layer that uses
them, with `lis`, `ori`, `sldi`, `oris` and `ori`. A left shift by `s` of a
value whose top `s` bits are zero (after masking) is written as a rotation
right by `64 - s`, which is the same.

Every block here writes only the state registers, the temporaries `t0`,
`t1`, `t2` and the mask registers (all among the S-box's temporaries), and
AddRoundKey loads the round key from `kp`. None uses memory otherwise.
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE

open VG.PPC64LE

/-- The temporaries. -/
def t0 : Reg := .r22
def t1 : Reg := .r23
def t2 : Reg := .r30

/-- The registers holding masks `1 … 6`. -/
def m : Nat → Reg
  | 1 => .r24 | 2 => .r25 | 3 => .r26 | 4 => .r27 | 5 => .r28 | _ => .r29

def rorI (d n : Reg) (k : Nat) : Instr := .rotr .d d n k
def shrI (d n : Reg) (k : Nat) : Instr := .lsr .d d n k

/-- `d := v`: `lis`, `ori`, `sldi 32`, `oris`, `ori`. The sign extension of
`lis` is shifted out. -/
def imm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- Build masks `k` in registers `m k`. -/
def setMasks (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.flatMap fun (k, v) => imm64 (m k) v

/-! ## Between bytes and the bitsliced state -/

/-- A delta swap within `x`: exchanges the bits of `x` in the mask `m k`
with the bits `s` places above them (`t0` is clobbered). -/
def swapIn (x : Reg) (k s : Nat) : List Instr :=
  [shrI t0 x s, xorR t0 t0 x, andR t0 t0 (m k), xorR x x t0, rorI t0 t0 (64 - s), xorR x x t0]

/-- A delta swap between `x` and `y` (BearSSL's `SWAPN`): exchanges the bits
of `y` in the mask `m k` with the bits of `x` `s` places above them. -/
def swapBetween (x y : Reg) (k s : Nat) : List Instr :=
  [shrI t0 x s, xorR t0 t0 y, andR t0 t0 (m k), xorR y y t0, rorI t0 t0 (64 - s), xorR x x t0]

/-- The masks of the transposes. -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00), (3, 0x00FF00FF00FF00FF),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]

/-- Bytes `0 1 2 3 4 5 6 7` of each word become `0 4 1 5 2 6 3 7`. -/
def zip1 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) 1 16
def zip2 : List Instr := (List.range 8).flatMap fun k => swapIn (q k) 2 8

/-- Interleave the bytes of `q b` and `q (b + 4)`. -/
def swap8 : List Instr := (List.range 4).flatMap fun b => swapBetween (q b) (q (b + 4)) 3 8

/-- BearSSL's `br_aes_ct64_ortho`: transposes the 8×8 bit matrix in each
byte position of the eight words. -/
def ortho : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 4 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 5 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapBetween (q a) (q b) 6 4)

/-- From four blocks (block `b`'s bytes 0–7 in `q b` and 8–15 in `q (b + 4)`,
little-endian) to the bitsliced state. -/
def toBs : List Instr := setMasks bsMasks ++ zip1 ++ zip2 ++ swap8 ++ ortho

/-- From the bitsliced state back to four blocks, as `toBs` takes them. -/
def fromBs : List Instr := setMasks bsMasks ++ ortho ++ swap8 ++ zip2 ++ zip1

/-! ## The round transformations -/

/-- The masks of ShiftRows. -/
def srMasks : List (Nat × BitVec 64) :=
  [(1, 0x0000FFFF0000FFFF), (2, 0x0FFF00000FFF0000), (3, 0xF0000000F0000000),
   (4, 0x00000000FFFFFFFF), (5, 0x00FF00FF00000000), (6, 0xFF00FF0000000000)]

/-- ShiftRows of one word: rows 1 and 3 rotate by 4 bits within their 16
bits, then rows 2 and 3 by 8. -/
def srWord (x : Reg) : List Instr :=
  [rorI t0 x 4, andR t0 t0 (m 2), rorI t1 x 52, andR t1 t1 (m 3),
   andR x x (m 1), xorR x x t0, xorR x x t1,
   rorI t0 x 8, andR t0 t0 (m 5), rorI t1 x 56, andR t1 t1 (m 6),
   andR x x (m 4), xorR x x t0, xorR x x t1]

def shiftRows : List Instr :=
  setMasks srMasks ++ (List.range 8).flatMap fun j => srWord (q j)

/-- The register holding `u₇ = q₇ ⊕ (q₇ ⋙ 16)` during MixColumns. -/
def u7 : Reg := .r24

/-- The register that output word `j` of MixColumns is computed in. -/
def mcOut (j : Nat) : Reg := if j = 0 then t0 else if j = 1 then t1 else q (j - 2)

/-- Output word `j` of MixColumns (BearSSL's `mix_columns`): with
`rⱼ = qⱼ ⋙ 16` (the next row) and `uⱼ = qⱼ ⊕ rⱼ`, it is
`uⱼ₋₁ ⊕ [j ∈ {0, 1, 3, 4}] u₇ ⊕ rⱼ ⊕ (uⱼ ⋙ 32)` (the multiplication by
`{02}` of `uⱼ` moves bit `j - 1` to `j` and reduces by `{1b}`). `q (j - 1)`
holds `uⱼ₋₁`, and `q j` is left holding `uⱼ`. -/
def mcWord (j : Nat) : List Instr :=
  ([rorI (mcOut j) (q j) 16, xorR (q j) (q j) (mcOut j)] : List Instr) ++
  (if j = 0 then [] else [xorR (mcOut j) (mcOut j) (q (j - 1))]) ++
  (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [xorR (mcOut j) (mcOut j) u7] else []) ++
  ([rorI t2 (q j) 32, xorR (mcOut j) (mcOut j) t2] : List Instr)

def mixColumns : List Instr :=
  ([rorI u7 (q 7) 16, xorR u7 u7 (q 7)] : List Instr) ++
  (List.range 8).flatMap mcWord ++
  ((List.range 8).reverse.map fun j => movR (q j) (mcOut j))

/-- The register pointing to the round key. -/
def kp : Reg := .r4

/-- AddRoundKey, with the bitsliced round key at `kp`. -/
def addRoundKey : List Instr :=
  (List.range 8).flatMap fun j => [.load .d t0 kp (8 * j), xorR (q j) (q j) t0]

end VG.Impl.Aes.PPC64LE
