import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified

/-! # A power in curve448's field, in radix `2^56`, on AArch64 -/

namespace VG.Artifacts.Gf448R56.AArch64

open VG.Spec.X448.Field56 VG.Impl.Ed448.AArch64.Point56 VG.Proof.Ed448.AArch64.Point56

def artifacts : List Artifact := [
  { powApi with
    target := AArch64.target
    doc := powApi.doc (notes := ["Uses baseline integer instructions, and AdvSIMD moves to keep \
      `x19` and `x21` to `x28` in lanes of `v16` to `v20` while it runs. Runs X448's inversion \
      chain up to `a^(2^223 - 1)`, then 223 squarings and a product, with `vg_x448`'s field \
      products (eight 56-bit limbs in 64-bit words), the squarings in loops counted by `x19`."])
    code := powFn
    contract := powContract AArch64.abi
    verified := powFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gf448R56.AArch64
