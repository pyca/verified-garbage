import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Arm.PointCurves

/-!
# P-192's point addition and doubling on 32-bit ARM

`vg_p192_point_add` and `vg_p192_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
P-192's prime. A generic file (see `TCB/Emit.lean`) over P-192's group law
`h`, the variant `Variants/P192/Arm/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

namespace VG.Generic.P192.Arm.PointP192

open VG.Proof.Weierstrass.Arm.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `lr` in its own working space and keeps `ws` in \
  `r12`, and computes Renes, Costello and Batina's 40 steps by calls of `vg_p192_mul_mod_p`, \
  `vg_p192_add_mod_p` and `vg_p192_sub_mod_p` on fixed offsets of `ws`, `movw` immediates in \
  `r1`–`r3`. It writes no register but `r0`–`r3`, `r12` and `lr`."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  { Spec.Weierstrass.Point.p192.addApi with
    target := Arm.target
    doc := Spec.Weierstrass.Point.p192.addApi.doc (notes := notes)
    code := Impl.Weierstrass.Arm.Point.pointAdd Spec.Weierstrass.Point.p192
    contract := Spec.Weierstrass.Point.p192.addContract Arm.abi
    verified := p192_add_verified (fermat_of_law h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Weierstrass.Point.p192.doubleApi with
    target := Arm.target
    doc := Spec.Weierstrass.Point.p192.doubleApi.doc (notes := notes)
    code := Impl.Weierstrass.Arm.Point.pointDouble Spec.Weierstrass.Point.p192
    contract := Spec.Weierstrass.Point.p192.doubleContract Arm.abi
    verified := p192_double_verified (fermat_of_law h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P192.Arm.PointP192
