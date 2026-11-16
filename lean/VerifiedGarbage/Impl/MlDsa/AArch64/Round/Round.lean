module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

/-!
# ML-DSA on AArch64: `vg_mldsa_norm_lt`, and the constants of `Decompose`

`vg_mldsa_norm_lt` runs one loop over the 256 coefficients (`mapLoop`), with
a counter counting down from 256 and the pointer of the polynomial advancing
by 4 bytes from coefficient 0. There is no branch on data: a conditional
step uses the sign bit of a 64-bit difference (`lsr #63`).

* `normLt(f = x0, bound = w1)`: the top bit of `x10` stays set while every
  coefficient `a` so far has `a < bound` or `q - a < bound` (both
  differences, in 64 bits, negative for one of them); it is the result.

`Decompose` divides by `2γ₂` with a multiplication and shifts, as the
reference implementation does:
`f = ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` for `(M, S)` = `(1025, 22)` if
`γ₂ = (q - 1)/32` and `(11275, 24)` if `γ₂ = (q - 1)/88` (`dMul`, `dShift`),
which is `⌊(a + γ₂ - 1)/(2γ₂)⌋` for every `a < q`; then `r₁ = f mod m` for
`m = (q - 1)/(2γ₂)` (`dMod`: 16 or 44). `γ₂` is a public argument: a
function that takes it zero-extends it (`zext`: it is a `u32`), compares it
with `(q - 1)/32` and branches on it once (`onGamma`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Round

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov csub)
open VG.Impl.MlDsa.AArch64.Arith (movW qNat)

/-- The loop over the coefficients: `body`, then the pointers `ptrs` advance
and the counter `cnt` counts down from 256. -/
def mapLoop (ptrs : List Reg) (cnt : Reg) (body : List Instr) : Prog isa :=
  .seq (.block [.movz .x cnt 256 0])
    (.loop (.block (body ++ ptrs.map (fun p => .addImm .x p p 4) ++ ([.subImm .x cnt cnt 1] : List Instr)))
      (.nonzero .x cnt))

/-! ## `Decompose` -/

/-- The values of `γ₂`: `(q - 1)/32` and `(q - 1)/88`. -/
def g32 : Nat := 261888
def g88 : Nat := 95232

/-- The multiplier `M`. -/
def dMul (g : Nat) : Nat := if g = 261888 then 1025 else 11275

/-- The shift `S`. -/
def dShift (g : Nat) : Nat := if g = 261888 then 22 else 24

/-- `m = (q - 1)/(2γ₂)`. -/
def dMod (g : Nat) : Nat := if g = 261888 then 16 else 44

/-- The branch on `γ₂` (in `gr`, zero-extended), through `t`: `arm g32` if
it is `(q - 1)/32`, else `arm g88`. -/
def onGamma (gr t : Reg) (arm : Nat → Prog isa) : Prog isa :=
  .seq (.block (movW t (BitVec.ofNat 32 g32) ++ ([.sub .x t gr t] : List Instr))) (.ite (.zero .x t) (arm g32) (arm g88))

/-- `γ₂` in `gr` zero-extended first, then `main`. -/
def zext (gr : Reg) (main : Prog isa) : Prog isa := .seq (.block [.addImm .w gr gr 0]) main

/-! ## `normLt` -/

def nlBody : List Instr :=
  [.ldr .w .x12 .x0 0, .sub .x .x13 .x12 .x1, .sub .x .x14 .x9 .x12, .sub .x .x14 .x14 .x1,
    .logic .orr .x .x13 .x13 .x14, .logic .and .x .x10 .x10 .x13]

def normLt : Prog isa :=
  .seq (.block (([.addImm .w .x1 .x1 0] : List Instr) ++ movW .x9 (BitVec.ofNat 32 qNat) ++
      ([.movz .x .x10 0 0, .subImm .x .x10 .x10 1] : List Instr)))
    (.seq (mapLoop [.x0] .x11 nlBody) (.block [.lsr .x .x0 .x10 63]))

end VG.Impl.MlDsa.AArch64.Round
