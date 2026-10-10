import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified

/-! # Ed448's point addition and doubling, in radix `2^56`, on AArch64 -/

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
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448R56.AArch64
