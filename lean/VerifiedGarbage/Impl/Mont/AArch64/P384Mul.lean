/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

The schedule is adapted from s2n-bignum's `bignum_montmul_p384_alt`
(`arm/p384/bignum_montmul_p384_alt.S`), as distributed in AWS-LC
(aws-lc-sys 0.45.0, `third_party/s2n-bignum/s2n-bignum-imported`): the full
product, then six short Montgomery reductions of its low half (the `montreds`
macro), then the high half added. The Lean representation and proofs are
maintained by verified-garbage.
-/
module

public import VerifiedGarbage.Impl.Mont.AArch64

/-!
# The core of P-384's Montgomery product modulo `p` on AArch64

`[a] [b] 2^-384 mod p`, for `p = 2^384 - 2^128 - 2^96 + 2^32 - 1`, with `[b]`
in `bRegs384` and `[a]` read through `x27`:

1. `prod`: the 12-word product into `accRegs`, row by row (`row`, as the
   word-by-word products: row `i` adds `a_i [b]` to words `i` to `i + 6`;
   the first sets words `0` to `6`, `rowInit`);
2. `redConsts` and `reds`: six short reductions of the low half
   (`montreds`): with `w = d₀ (2^32 + 1) mod 2^64`, so that `d₀ + w p` is a
   multiple of `2^64`, the low six words `[d₅ … d₀]` become
   `[d₆ d₅ … d₁] = ([d₅ … d₀] + w p) / 2^64`, the word `d₀`'s register
   holding the new top word `d₆`. Its terms are `w 2^384` (the top word,
   `w` itself) and `(2^384 - p) w`, subtracted: `2^384 - p` is
   `0xffffffff00000001` and `0x00000000ffffffff` in its two low words, then `1`,
   so three products (`umulh`, `mul`, `umulh`) give it;
3. `addHigh`: the high half added to the reduced low half, the carry into
   `x21`.

The caller loads `[b]`, then reduces the result below `p` and stores it.
-/

@[expose] public section

namespace VG.Impl.Mont.AArch64.P384Mul
open VG.AArch64

/-- The registers holding `[b]`. -/
def bRegs384 : List Reg := [.x4, .x5, .x16, .x17, .x21, .x22]

/-- The 12-word accumulator: the low half, then the high half. -/
def accRegs : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x6, .x23, .x24, .x25]

/-- The pointer to `[a]`. -/
def ra : Reg := .x27

/-- The low half's registers. -/
def lowRegs : List Reg := accRegs.take 6

/-- The high half's registers. -/
def highRegs : List Reg := accRegs.drop 6

/-- The accumulator's words `i` to `i + 6`, which row `i` adds to. -/
def rowRegs (i : Nat) : List Reg := (accRegs.drop i).take 7

/-- The product `[a] [b]` into `accRegs`: six rows, each from one word of
`[a]` loaded into `x1`, the first straight into the low seven words
(`rowInit`), so that only the high half is cleared first. -/
def prod : List Instr :=
  zeros highRegs ++ (.ldr .x .x1 ra 0 :: rowInit ra .x1 (rowRegs 0) bRegs384) ++
    (List.range 5).flatMap fun i =>
      .ldr .x .x1 ra (8 * (1 + i)) :: row ra .x1 (rowRegs (1 + i)) (bRegs384.map fun r => .gen (.reg r))

/-- `x16 = 0xffffffff00000001` and `x17 = 0x00000000ffffffff`, the low words
of `2^384 - p`, from `x7 = 0`. -/
def redConsts : List Instr :=
  [.subImm .x .x17 .x7 1, .lsl .x .x16 .x17 32, .lsr .x .x17 .x17 32, .addImm .x .x16 .x16 1]

/-- One short reduction of `[d₅ … d₀]` (`montreds`): `w = d₀ + d₀ 2^32` into
`d₀`'s register (the new top word), `[x3 x2 x1] = (2^384 - p) w / 2^64`, and
`[d₀ d₅ … d₁] = [w d₅ … d₁] - [x3 x2 x1]`. -/
def montreds (d₀ d₁ d₂ d₃ d₄ d₅ : Reg) : List Instr :=
  [.lsl .x .x1 d₀ 32, .add .x d₀ .x1 d₀,
   .umulh .x1 .x16 d₀, .mul .x .x3 .x17 d₀, .umulh .x2 .x17 d₀,
   .adds .x .x1 .x1 .x3, .adcs .x .x2 .x2 d₀, .adc .x .x3 .x7 .x7,
   .subs .x d₁ d₁ .x1, .sbcs .x d₂ d₂ .x2, .sbcs .x d₃ d₃ .x3,
   .sbcs .x d₄ d₄ .x7, .sbcs .x d₅ d₅ .x7, .sbc .x d₀ d₀ .x7]

/-- The low half's register for word `j` after `k` reductions. -/
def lowAt (k j : Nat) : Reg := lowRegs.getD ((k + j) % 6) .x8

/-- Reduction `k`, on the low half as the previous ones left it. -/
def red (k : Nat) : List Instr :=
  montreds (lowAt k 0) (lowAt k 1) (lowAt k 2) (lowAt k 3) (lowAt k 4) (lowAt k 5)

/-- The six reductions; after them the low half's words are in `lowRegs`
again, in order. -/
def reds : List Instr := redConsts ++ (List.range 6).flatMap red

/-- `ts += hs`, word by word, `adds` on the first word and `adcs` on the others. -/
def addsIn (first : Bool) : List Reg → List Reg → List Instr
  | t :: ts, h :: hs => (if first then .adds .x t t h else .adcs .x t t h) :: addsIn false ts hs
  | _, _ => []

/-- `[x21; low] = low + high`. -/
def addHigh : List Instr := addsIn true lowRegs highRegs ++ [.adc .x .x21 .x7 .x7]

end VG.Impl.Mont.AArch64.P384Mul
