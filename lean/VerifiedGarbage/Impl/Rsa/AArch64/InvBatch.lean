module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-!
# RSA private keys on AArch64: the loops of the batched inverse

The loops over the words of `Keys.inverse`'s batches of divsteps
(`Impl/Rsa/AArch64/Keys.lean`), each counting `x14` down by `countLoop`:

* `fgBody`, `deBody`: a word of a batch's fused passes over `(f, g)` and over
  `(a, b)`, both rows at once (see below).
* `cnegBody`: `[x16] := -[x16]` in place where the mask `x15` is all ones:
  `([x16] ^ x15) + 1` with the carry chain started from the mask.
-/
@[expose] public section

namespace VG.Impl.Rsa.AArch64.InvBatch

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- A word of `[x16] := ([x16] ^ x15) + C` (`x7 = 0`). -/
def cnegBody : List Instr :=
  [ld .x3 .x16, .logic .eor .x .x3 .x3 .x15, .adcs .x .x3 .x3 .x7, st .x3 .x16, next .x16]

/-- A word of `[x5] := 2 [x17]`'s chain: `[x16] := [x17] + [x17] + C`. -/
def dblBody : List Instr := [ld .x3 .x17, .adcs .x .x3 .x3 .x3, st .x3 .x16, next .x17, next .x16]

/-- `x14 := x11 · 2^32 + x12`: the stride and the count kept through the
divsteps, which leave only `x14`, `x15` and `x0`. -/
def packW : List Instr := [.lsl .x .x14 .x11 32, .add .x .x14 .x14 .x12]

/-- `x11`, `x12` back from `x14` (through `x13`). -/
def unpackW : List Instr := [.lsr .x .x11 .x14 32, .lsl .x .x13 .x11 32, .sub .x .x12 .x14 .x13]

/-- `x15 := 3 n + 2`, the batches, for `n` in `x12`. -/
def batchCount : List Instr := [.add .x .x15 .x12 .x12, .add .x .x15 .x15 .x12, .addImm .x .x15 .x15 2]

/-- `x15 := 15 n + 10`, the doublings: `5` per batch. -/
def dblCount : List Instr := [.lsl .x .x15 .x12 4, .sub .x .x15 .x15 .x12, .addImm .x .x15 .x15 10]

/-! ## The fused batch

A batch's two rows over `(f, g)` and over `(a, b)`, each in one pass over
the words, in place: the pointers lag a word behind what they read, so that
word `i` of each output is written once word `i + 1` of each input is read.
The matrix `u, v, q, r` is in `x4`–`x7`, its sign masks in `x9`, `x10`,
`x19`, `x20`. A row's word is the signed 128-bit sum of its two products
(`umulh` less the word where the coefficient is negative) and its signed
carry (`x13`, `x25`), whose high word is the next carry. Over `(f, g)` each
output word is the sum's words `i` and `i + 1` shifted by 59 (the previous
sum word in `x26`, `x27`); over `(a, b)` it is the sum's word `i + 1`, the
sum less its low word being `u a + v b + k m` for `k` (`x26`, `x27`) the
multiple of `m` that clears the low word: `k m`'s words go on an unsigned
carry of their own (`x23`, `x30`, with `x28` the zero register), so that
`x11`, `x12` and `x15` stay public in general-purpose registers. -/

/-- `x4`–`x7` := the matrix from the lanes of `v16`, `v17`, and `x9`, `x10`,
`x19`, `x20` := their sign masks (`x13 := 0`). -/
def coefMasks4 : List Instr :=
  [.umov .x .x4 .v16 0, .umov .x .x5 .v16 1, .umov .x .x6 .v17 0, .umov .x .x7 .v17 1, movi .x13 0, .lsr .x .x9 .x4 63, .sub .x .x9 .x13 .x9, .lsr .x .x10 .x5 63, .sub .x .x10 .x13 .x10,
    .lsr .x .x19 .x6 63, .sub .x .x19 .x13 .x19, .lsr .x .x20 .x7 63, .sub .x .x20 .x13 .x20]

/-- `lo + 2^64 H := c₁ [x2] + c₂ [x3]`, signed: `c₁`, `c₂` with their masks
(`Divstep.rowWord`). -/
def prods (c₁ c₂ m₁ m₂ lo : Reg) : List Instr :=
  [.mul .x lo c₁ .x2, .umulh .x21 c₁ .x2, .logic .and .x .x22 .x2 m₁, .sub .x .x21 .x21 .x22,
    .umulh .x23 c₂ .x3, .logic .and .x .x22 .x3 m₂, .sub .x .x23 .x23 .x22, .mul .x .x22 c₂ .x3,
    .adds .x lo lo .x22, .adc .x .x21 .x21 .x23]

/-- `prods` through `x21`, `x22` alone: the low words' sum first, its carry
kept in the flags through the high words (`umulh`, `and` and `sub` leave
them). -/
def prodsD (c₁ c₂ m₁ m₂ lo : Reg) : List Instr :=
  [.mul .x lo c₁ .x2, .mul .x .x22 c₂ .x3, .adds .x lo lo .x22, .umulh .x21 c₁ .x2, .umulh .x22 c₂ .x3,
    .adc .x .x21 .x21 .x22, .logic .and .x .x22 .x2 m₁, .sub .x .x21 .x21 .x22, .logic .and .x .x22 .x3 m₂,
    .sub .x .x21 .x21 .x22]

/-- `lo + 2^64 c += k [x8 + off] + kc`, the high word of the last two into
`kc` (`x28 = 0`). -/
def kterm (k kc c lo : Reg) (off : Nat) : List Instr :=
  [ld .x22 .x8 off, .umulh .x21 k .x22, .mul .x .x22 k .x22, .adds .x .x22 .x22 kc, .adc .x kc .x21 .x28,
    .adds .x lo lo .x22, .adc .x c c .x28]

/-- `lo + 2^64 c := lo + 2^64 H + c`, `c` signed. -/
def carryIn (c lo : Reg) : List Instr :=
  [.lsr .x .x22 c 63, .subImm .x .x22 .x22 1, .adds .x lo lo c, .sbc .x c .x21 .x22]

/-- A row's word over `(f, g)`. -/
def fgRow (c₁ c₂ m₁ m₂ c lo : Reg) : List Instr := prods c₁ c₂ m₁ m₂ lo ++ carryIn c lo

/-- A row's word over `(a, b)`, `m`'s word at `x8 + off`. -/
def deRow (c₁ c₂ m₁ m₂ k kc c lo : Reg) (off : Nat) : List Instr :=
  prodsD c₁ c₂ m₁ m₂ lo ++ carryIn c lo ++ kterm k kc c lo off

/-- The carry `c` less `c₁` where the top word `[x2]` is negative and `c₂`
where `[x3]` is: the passes take every word unsigned, the top words signed. -/
def topFix (c c₁ c₂ : Reg) : List Instr :=
  [.lsr .x .x22 .x2 63, .lsr .x .x23 .x3 63, movi .x21 0, .sub .x .x22 .x21 .x22, .sub .x .x23 .x21 .x23,
    .logic .and .x .x22 .x22 c₁, .logic .and .x .x23 .x23 c₂, .sub .x c c .x22, .sub .x c c .x23]

/-- Word `n` of a row over `(a, b)`: `m`'s word `n` is not read, and the
unsigned carry goes into the signed one. -/
def deRowTop (c₁ c₂ m₁ m₂ kc c lo : Reg) : List Instr :=
  prodsD c₁ c₂ m₁ m₂ lo ++ carryIn c lo ++ [.adds .x lo lo kc, .adc .x c c .x28]

/-- Word `n` of the pass over `(a, b)` (`[x16]`, `[x17]` at word `n - 1`). -/
def deTop : List Instr :=
  [ld .x2 .x16 8, ld .x3 .x17 8] ++ deRowTop .x4 .x5 .x9 .x10 .x23 .x13 .x1 ++ [st .x1 .x16] ++
  deRowTop .x6 .x7 .x19 .x20 .x30 .x25 .x24 ++ [st .x24 .x17, next .x16, next .x17]

/-- Word `i ≥ 1` of the pass over `(f, g)` (`[x16]`, `[x17]` at word `i - 1`). -/
def fgBody : List Instr :=
  [ld .x2 .x16 8, ld .x3 .x17 8] ++ fgRow .x4 .x5 .x9 .x10 .x13 .x1 ++ fgRow .x6 .x7 .x19 .x20 .x25 .x24 ++
  [.extr .x .x22 .x1 .x26 59, st .x22 .x16, mov .x26 .x1, .extr .x .x22 .x24 .x27 59, st .x22 .x17,
    mov .x27 .x24, next .x16, next .x17]

/-- Word `1 ≤ i < n` of the pass over `(a, b)` (`[x16]`, `[x17]`, `[x8] = m` at word `i - 1`). -/
def deBody : List Instr :=
  [ld .x2 .x16 8, ld .x3 .x17 8] ++ deRow .x4 .x5 .x9 .x10 .x26 .x23 .x13 .x1 8 ++
  deRow .x6 .x7 .x19 .x20 .x27 .x30 .x25 .x24 8 ++ [st .x1 .x16, st .x24 .x17, next .x16, next .x17, next .x8]

end VG.Impl.Rsa.AArch64.InvBatch
