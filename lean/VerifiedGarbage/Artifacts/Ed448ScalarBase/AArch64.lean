import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified

/-!
# Ed448 base-point multiplication on AArch64

The signature and documentation come from the reviewed Ed448 API.
-/

namespace VG.Artifacts.Ed448ScalarBase.AArch64

def artifacts : List Artifact := [
  { Spec.Ed448.scalarBaseApi with
    target := AArch64.target
    doc := Spec.Ed448.scalarBaseApi.doc (notes := ["Computes `[s] B` with `vg_x448_base`'s comb \
      over all 57 bytes of the scalar: its 114 signed radix-16 digits select, in constant time \
      (reading every entry), entries `[m 256^j] B` (`m ≤ 8`) of 57 tables in the static \
      `VG_X448_COMB`, added to two projective \
      accumulators with RFC 8032's complete addition (a call of `vg_ed448_r56_comb_base`), then \
      `16 A + B` by five calls of `vg_ed448_r56_point_add`. `Z` is inverted with \
      X448's addition chain for `p - 2`. Field elements are eight 56-bit limbs, multiplied as \
      `vg_x448`'s are. The function saves its caller's callee-saved registers in `scratch`."])
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.Ed448.AArch64.scalarBase
    contract := Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts)
    verified := Proof.Ed448.AArch64.scalarBase_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448ScalarBase.AArch64
