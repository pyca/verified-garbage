import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified
import VerifiedGarbage.Proof.Ed448.AArch64.CombBase

/-! # Ed448's point addition and doubling and its fixed-base comb, in radix `2^56`, on AArch64 -/

namespace VG.Artifacts.Ed448R56.AArch64

open VG.Spec.Ed448.Point56 VG.Impl.Ed448.AArch64.Point56 VG.Proof.Ed448.AArch64.Point56

/-- How the functions work. -/
def notes (formula : String) : List String := ["Uses baseline integer instructions, and \
  AdvSIMD moves to keep `x21` to `x28` in lanes of `v16` to `v19` while it runs. " ++ formula ++
  " as `vg_ed448_verify_equation` inlined it, with `vg_x448`'s field products (eight 56-bit limbs \
  in 64-bit words), the temporaries in slots 10 to 18."]

def artifacts : List Artifact := [
  { addApi with
    target := AArch64.target
    doc := addApi.doc (notes := notes "Runs RFC 8032's complete addition formula, twelve products")
    code := addFn
    contract := addContract AArch64.abi
    verified := addFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { doubleApi with
    target := AArch64.target
    doc := doubleApi.doc (notes := notes "Runs RFC 8032's doubling formulas, eight products")
    code := doubleFn
    contract := doubleContract AArch64.abi
    verified := doubleFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ed448.Comb56.combBaseApi with
    target := AArch64.target
    doc := Spec.Ed448.Comb56.combBaseApi.doc (notes := ["Uses baseline integer instructions and \
      AdvSIMD. The comb of `vg_x448_base`, `vg_ed448_scalar_base` and `vg_ed448_verify_equation`: \
      the scalar's signed radix-16 digits select, in constant time (reading every entry), entries \
      `[m 256^j] B` (`m ≤ 8`) of `n` tables in the static `VG_X448_COMB`, added to two projective \
      accumulators starting at `[G] B` for `G = 8 Σ_{j < n} 256^j`, with RFC 8032's complete \
      addition (four pairs of the field products in AdvSIMD, each interleaved with independent \
      scalar products), so that the accumulators are `A` and `C`. Field elements are eight 56-bit \
      limbs, multiplied as `vg_x448`'s are. The products use every vector register, so the \
      function keeps `x21` to `x28` in the upper halves of `v8` to `v15` and stores those in its \
      own working space (bytes 3968 to 4095), and keeps `x19` and the return address after slot \
      21's element (bytes 2816 to 2831), while it runs."])
    consts := VG.Impl.X448.AArch64.Base.combConsts
    code := VG.Impl.Ed448.AArch64.CombBase.combBaseFn
    contract := Spec.Ed448.Comb56.combBaseContract (AArch64.abi.withConsts VG.Impl.X448.AArch64.Base.combConsts)
    verified := VG.Proof.Ed448.AArch64.CombBase.combBaseFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448R56.AArch64
