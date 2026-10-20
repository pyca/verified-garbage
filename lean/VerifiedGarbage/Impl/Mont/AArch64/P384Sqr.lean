/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

The schedule is adapted from s2n-bignum's `bignum_montsqr_p384_alt`
(`arm/p384/bignum_montsqr_p384_alt.S`), as distributed in AWS-LC
(aws-lc-sys 0.45.0, `third_party/s2n-bignum/s2n-bignum-imported`): the
products of distinct words once, doubled, then the squares of the words added,
then the reductions of `bignum_montmul_p384_alt` (`P384Mul`). The Lean
representation and proofs are maintained by verified-garbage.
-/
module

public import VerifiedGarbage.Impl.Mont.AArch64.P384Mul

/-!
# The core of P-384's Montgomery square modulo `p` on AArch64

`[a]^2 2^-384 mod p`, with `[a]` in `aRegs` (`P384Mul.bRegs384`):

1. `offDiag`: the products `a_i a_j` of distinct words, `i < j`, into the
   accumulator (`P384Mul.accRegs`, cleared first): a `row` for each `i < 5`,
   adding `a_i [a_(i+1) … a_5]` to words `2i + 1` to `6 + i`;
2. `dbl`: the accumulator doubled;
3. `diag`: the squares `a_i^2` added at words `2i` and `2i + 1`;
4. then `P384Mul.reds` and `P384Mul.addHigh`, as for the product.
-/

@[expose] public section

namespace VG.Impl.Mont.AArch64.P384Sqr
open VG.AArch64 VG.Impl.Mont.AArch64

/-- The registers holding `[a]`. -/
abbrev aRegs : List Reg := P384Mul.bRegs384

/-- Row `i`'s words of the accumulator: `2i + 1` to `6 + i`. -/
def sqRowRegs (i : Nat) : List Reg := (P384Mul.accRegs.drop (2 * i + 1)).take (6 - i)

/-- Row `i`: `a_i [a_(i+1) … a_5]` added at word `2i + 1`. Its words are
registers, so the row's base register `rm` is never read. -/
def sqRowAt (rm : Reg) (i : Nat) : List Instr :=
  row rm (aRegs.getD i .x4) (sqRowRegs i) ((aRegs.drop (i + 1)).map fun r => .gen (.reg r))

/-- The products of distinct words, from a cleared accumulator. -/
def offDiagAt (rm : Reg) : List Instr := zeros P384Mul.accRegs ++ (List.range 5).flatMap (sqRowAt rm)

/-- `ts += ts`: `adds` on the first word, `adcs` on the others. -/
def dblIn (first : Bool) : List Reg → List Instr
  | [] => []
  | t :: ts => (if first then .adds .x t t t else .adcs .x t t t) :: dblIn false ts

/-- The accumulator doubled. -/
def dbl : List Instr := dblIn true P384Mul.accRegs

/-- `a_i^2` added at words `2i` and `2i + 1`, through `x2`, the carry rippling. -/
def diagIn (first : Bool) : List Reg → List Reg → List Instr
  | a :: as, lo :: hi :: ts =>
    [.mul .x .x2 a a, if first then .adds .x lo lo .x2 else .adcs .x lo lo .x2,
      .umulh .x2 a a, .adcs .x hi hi .x2] ++ diagIn false as ts
  | _, _ => []

/-- The squares of the words added. -/
def diag : List Instr := diagIn true aRegs P384Mul.accRegs

/-- The square, `[acc] = [a]^2`, its rows on the base register `rm`. -/
def sqAt (rm : Reg) : List Instr := offDiagAt rm ++ dbl ++ diag

/-- The square, as `vg_p384_sqr_mod_p` computes it. -/
def sq : List Instr := sqAt .x27

end VG.Impl.Mont.AArch64.P384Sqr
