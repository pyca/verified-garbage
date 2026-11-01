module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-!
# RSA private keys on AArch64: the loops of the batched inverse

The loops over the words of `Keys.inverse`'s batches of divsteps
(`Impl/Rsa/AArch64/Keys.lean`), each counting `x14` down by `countLoop`:

* `rowBody`: `[x8] := x4 [x16] + x5 [x17]` modulo `2^(64 k)` for `k` words,
  `x4` and `x5` signed (their sign masks in `x9`, `x10`), the words of
  `[x16]` and `[x17]` taken unsigned: each word's two products as signed
  128-bit numbers (`umulh` less the word where the coefficient is negative),
  plus the signed carry in `x13`, whose high word is the next carry
  (`sbc` against `(x13 >> 63) - 1` adds its sign). `[x8]` may be `[x17]`:
  each word is read before it is written.
* `shrBody`, `shrTop`: `[x17] := [x16] >> 59`, arithmetic, word `i` from words
  `i` and `i + 1` and the top word from its sign; `[x17]` may be `[x16]`.
* `copyBody`: `[x17] := [x16]` word by word, ascending, so `[x16]` may be
  `[x17]` plus some words.
* `cnegBody`: `[x16] := -[x16]` in place where the mask `x15` is all ones:
  `([x16] ^ x15) + 1` with the carry chain started from the mask.
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.InvBatch

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- `x9`, `x10` := the sign masks of `x4`, `x5`, and `x13 := 0`. -/
def coefMasks : List Instr :=
  [movi .x13 0, .lsr .x .x9 .x4 63, .sub .x .x9 .x13 .x9, .lsr .x .x10 .x5 63, .sub .x .x10 .x13 .x10]

/-- A word of `[x8] := x4 [x16] + x5 [x17]`, the signed carry in `x13`. -/
def rowBody : List Instr :=
  [ld .x2 .x16, ld .x3 .x17, .mul .x .x6 .x4 .x2, .umulh .x7 .x4 .x2, .logic .and .x .x2 .x2 .x9,
    .sub .x .x7 .x7 .x2, .mul .x .x2 .x5 .x3, .umulh .x1 .x5 .x3, .logic .and .x .x3 .x3 .x10,
    .sub .x .x1 .x1 .x3, .lsr .x .x3 .x13 63, .subImm .x .x3 .x3 1, .adds .x .x6 .x6 .x2,
    .adc .x .x7 .x7 .x1, .adds .x .x6 .x6 .x13, .sbc .x .x13 .x7 .x3, st .x6 .x8, next .x16, next .x17,
    next .x8]

/-- A word of `[x17] := [x16] >> 59`, from words `i` and `i + 1`. -/
def shrBody : List Instr :=
  [ld .x3 .x16, ld .x4 .x16 8, .extr .x .x3 .x4 .x3 59, st .x3 .x17, next .x16, next .x17]

/-- The top word of `[x17] := [x16] >> 59`, from its sign. -/
def shrTop : List Instr :=
  [ld .x3 .x16, .lsr .x .x4 .x3 63, movi .x13 0, .sub .x .x4 .x13 .x4, .extr .x .x3 .x4 .x3 59, st .x3 .x17]

/-- A word of `[x17] := [x16]`. -/
def copyBody : List Instr := [ld .x3 .x16, st .x3 .x17, next .x16, next .x17]

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

end VG.Impl.Rsa.AArch64.InvBatch
