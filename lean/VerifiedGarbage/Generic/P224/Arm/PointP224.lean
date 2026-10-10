import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves

/-!
# P-224's point addition and doubling on 32-bit ARM

`vg_p224_point_add` and `vg_p224_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
P-224's prime. A generic file (see `TCB/Emit.lean`) over P-224's group law
`h`, the variant `Variants/P224/Arm/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

namespace VG.Generic.P224.Arm.PointP224

open VG.Proof.Weierstrass.Arm.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `lr` in its own working space and keeps `ws` in \
  `r12`, and computes Renes, Costello and Batina's 40 steps by calls of `vg_p224_mul_mod_p`, \
  `vg_p224_add_mod_p` and `vg_p224_sub_mod_p` on fixed offsets of `ws`, `movw` immediates in \
  `r1`–`r3`. It writes no register but `r0`–`r3`, `r12` and `lr`."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  { Spec.Weierstrass.Point.p224.addApi with
    target := Arm.target
    doc := Spec.Weierstrass.Point.p224.addApi.doc (notes := notes)
    code := Impl.Weierstrass.Arm.Point.pointAdd Spec.Weierstrass.Point.p224
    contract := Spec.Weierstrass.Point.p224.addContract Arm.abi
    verified := p224_add_verified (fermat_of_law h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Weierstrass.Point.p224.doubleApi with
    target := Arm.target
    doc := Spec.Weierstrass.Point.p224.doubleApi.doc (notes := notes)
    code := Impl.Weierstrass.Arm.Point.pointDouble Spec.Weierstrass.Point.p224
    contract := Spec.Weierstrass.Point.p224.doubleContract Arm.abi
    verified := p224_double_verified (fermat_of_law h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P224.Arm.PointP224
