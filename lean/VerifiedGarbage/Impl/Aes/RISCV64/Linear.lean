module

public import VerifiedGarbage.Impl.Aes.RISCV64.Sbox

/-!
# The linear layers of bitsliced AES on RISC-V

As on PPC64LE (`Impl/Aes/PPC64LE/Linear.lean`): the state of four blocks is
eight 64-bit words in `q 0 … q 7`, word `j` holding bit `j` of the 64
bytes: byte `i = r + 4c` (row `r`, column `c`) of block `b` is at bit
position `16r + 4c + b`, as in BearSSL's `aes_ct64` (Thomas Pornin, MIT
licence), whose `ortho`, `interleave_in`, `shift_rows` and `mix_columns`
these follow. So ShiftRows rotates each 16-bit row, and MixColumns rotates
whole words by 16 and 32 bits.

RV64I has no rotation, and every rotation of ShiftRows and of the delta
swaps keeps only bits that a shift moves without wrapping around (the rest
are masked off), so it is a shift; MixColumns' rotations are a right shift
XORed with a left shift (through `rt`).

RV64I builds 64-bit constants in several instructions, so the masks are
built once, in the slots of the scratch buffer from `bsSlot`, `srSlot` and
`invSrSlot` on (`maskInit`), and each layer that uses them loads them into
registers (`m 1 … m 6`).

Every block here writes only the state registers, the temporaries `t0`,
`t1`, `t2` and `rt`, and the mask registers (all among the S-box's
temporaries), and AddRoundKey loads the round key from `kp`. None uses
memory otherwise.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64

/-- The temporaries. -/
def t0 : Reg := .t0
def t1 : Reg := .t1
def t2 : Reg := .t2

/-- The registers holding masks `1 … 6`. -/
def m : Nat → Reg
  | 1 => .t3 | 2 => .t4 | 3 => .t5 | 4 => .t6 | 5 => .a6 | _ => .a7

/-- The temporary of MixColumns' rotations (mask register 2, which
MixColumns does not use). -/
def rt : Reg := .t4

def shlI (d n : Reg) (k : Nat) : Instr := .shift .sll .d d n k
def shrI (d n : Reg) (k : Nat) : Instr := .shift .srl .d d n k

/-- `d := n ⋙ k`, through `rt`: `rt`, `n` and `d` are different. -/
def rorI (d n : Reg) (k : Nat) : List Instr := [shrI rt n k, shlI d n (64 - k), xorR d d rt]

/-- Load masks `k` into registers `m k` from the slots from `base` on. -/
def loadMasks (base : Nat) (ms : List (Nat × BitVec 64)) : List Instr :=
  ms.map fun (k, _) => ldS (m k) (base + k - 1)

/-! ## Between bytes and the bitsliced state -/

/-- A delta swap within `x`: exchanges the bits of `x` in the mask `m k`
with the bits `s` places above them (`t0` is clobbered). -/
def swapIn (x : Reg) (k s : Nat) : List Instr :=
  [shrI t0 x s, xorR t0 t0 x, andR t0 t0 (m k), xorR x x t0, shlI t0 t0 s, xorR x x t0]

/-- A delta swap between `x` and `y` (BearSSL's `SWAPN`): exchanges the bits
of `y` in the mask `m k` with the bits of `x` `s` places above them. -/
def swapBetween (x y : Reg) (k s : Nat) : List Instr :=
  [shrI t0 x s, xorR t0 t0 y, andR t0 t0 (m k), xorR y y t0, shlI t0 t0 s, xorR x x t0]

/-- The masks of the transposes, and their first slot. -/
def bsMasks : List (Nat × BitVec 64) :=
  [(1, 0x00000000FFFF0000), (2, 0x0000FF000000FF00), (3, 0x00FF00FF00FF00FF),
   (4, 0x5555555555555555), (5, 0x3333333333333333), (6, 0x0F0F0F0F0F0F0F0F)]
def bsSlot : Nat := 52

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
def toBs : List Instr := loadMasks bsSlot bsMasks ++ zip1 ++ zip2 ++ swap8 ++ ortho

/-- From the bitsliced state back to four blocks, as `toBs` takes them. -/
def fromBs : List Instr := loadMasks bsSlot bsMasks ++ ortho ++ swap8 ++ zip2 ++ zip1

/-! ## The round transformations -/

/-- The masks of ShiftRows, and their first slot. -/
def srMasks : List (Nat × BitVec 64) :=
  [(1, 0x0000FFFF0000FFFF), (2, 0x0FFF00000FFF0000), (3, 0xF0000000F0000000),
   (4, 0x00000000FFFFFFFF), (5, 0x00FF00FF00000000), (6, 0xFF00FF0000000000)]
def srSlot : Nat := 64

/-- ShiftRows of one word: rows 1 and 3 rotate by 4 bits within their 16
bits, then rows 2 and 3 by 8. -/
def srWord (x : Reg) : List Instr :=
  [shrI t0 x 4, andR t0 t0 (m 2), shlI t1 x 12, andR t1 t1 (m 3),
   andR x x (m 1), xorR x x t0, xorR x x t1,
   shrI t0 x 8, andR t0 t0 (m 5), shlI t1 x 8, andR t1 t1 (m 6),
   andR x x (m 4), xorR x x t0, xorR x x t1]

def shiftRows : List Instr :=
  loadMasks srSlot srMasks ++ (List.range 8).flatMap fun j => srWord (q j)

/-- The register holding `u₇ = q₇ ⊕ (q₇ ⋙ 16)` during MixColumns. -/
def u7 : Reg := .t3

/-- The register that output word `j` of MixColumns is computed in. -/
def mcOut (j : Nat) : Reg := if j = 0 then t0 else if j = 1 then t1 else q (j - 2)

/-- Output word `j` of MixColumns (BearSSL's `mix_columns`): with
`rⱼ = qⱼ ⋙ 16` (the next row) and `uⱼ = qⱼ ⊕ rⱼ`, it is
`uⱼ₋₁ ⊕ [j ∈ {0, 1, 3, 4}] u₇ ⊕ rⱼ ⊕ (uⱼ ⋙ 32)` (the multiplication by
`{02}` of `uⱼ` moves bit `j - 1` to `j` and reduces by `{1b}`). `q (j - 1)`
holds `uⱼ₋₁`, and `q j` is left holding `uⱼ`. -/
def mcWord (j : Nat) : List Instr :=
  rorI (mcOut j) (q j) 16 ++ ([xorR (q j) (q j) (mcOut j)] : List Instr) ++
  (if j = 0 then [] else [xorR (mcOut j) (mcOut j) (q (j - 1))]) ++
  (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [xorR (mcOut j) (mcOut j) u7] else []) ++
  rorI t2 (q j) 32 ++ ([xorR (mcOut j) (mcOut j) t2] : List Instr)

def mixColumns : List Instr :=
  rorI u7 (q 7) 16 ++ ([xorR u7 u7 (q 7)] : List Instr) ++
  (List.range 8).flatMap mcWord ++
  ((List.range 8).reverse.map fun j => movR (q j) (mcOut j))

/-- The register pointing to the round key. -/
def kp : Reg := .a1

/-- AddRoundKey, with the bitsliced round key at `kp`. -/
def addRoundKey : List Instr :=
  (List.range 8).flatMap fun j => [.load .d t0 kp (8 * j), xorR (q j) (q j) t0]

end VG.Impl.Aes.RISCV64
