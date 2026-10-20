module

public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.CombBase
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448's point addition and doubling and its fixed-base comb, in radix `2^56`, on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ed448R56.AArch64

open VG.Spec.Ed448.Point56 VG.Impl.Ed448.AArch64.Point56 VG.Proof.Ed448.AArch64.Point56

/-- How the functions work. -/
def notes (formula : String) : List String := ["Uses baseline integer instructions, and \
  AdvSIMD moves to keep `x21` to `x28` in lanes of `v16` to `v19` while it runs. " ++ formula ++
  " as `vg_ed448_verify_equation` inlined it, with `vg_x448`'s field products (eight 56-bit limbs \
  in 64-bit words), the temporaries in slots 10 to 18."]

def artifacts : List Artifact := [
  addApi.artifact AArch64.target {
    notes := notes "Runs RFC 8032's complete addition formula, twelve products"
    code := addFn
    verified := addFn_verified
    stack := 0 },
  doubleApi.artifact AArch64.target {
    notes := notes "Runs RFC 8032's doubling formulas, eight products"
    code := doubleFn
    verified := doubleFn_verified
    stack := 0 },
  Spec.Ed448.Comb56.combBaseApi.artifact AArch64.target {
    notes := ["Uses baseline integer instructions and \
      AdvSIMD. The comb of `vg_x448_base`, `vg_ed448_scalar_base` and `vg_ed448_verify_equation`: \
      the scalar's signed radix-16 digits select, in constant time (reading every entry), entries \
      `[m 256^j] B` (`m ≤ 8`) of `n` tables in the static `VG_X448_COMB`, added to two projective \
      accumulators starting at `[G] B` for `G = 8 Σ_{j < n} 256^j`, with RFC 8032's complete \
      addition (four pairs of the field products in AdvSIMD, each interleaved with independent \
      scalar products), so that the accumulators are `A` and `C`. Field elements are eight 56-bit \
      limbs, multiplied as `vg_x448`'s are. The products use every vector register, so the \
      function keeps `x21` to `x28` in the upper halves of `v8` to `v15` and stores those in its \
      own working space (bytes 3968 to 4095), and keeps `x19` and the return address after slot \
      21's element (bytes 2816 to 2831), while it runs."]
    consts := VG.Impl.X448.AArch64.Base.combConsts
    code := VG.Impl.Ed448.AArch64.CombBase.combBaseFn
    verified := VG.Proof.Ed448.AArch64.CombBase.combBaseFn_verified
    stack := 0 }]

end VG.Artifacts.Ed448R56.AArch64
