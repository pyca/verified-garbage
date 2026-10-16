module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.Arm.PointBrainpoolP256r1
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Spec.X25519

/-!
# brainpoolP256r1's point addition and doubling on 32-bit ARM

`vg_brainpoolp256r1_point_add` and `vg_brainpoolp256r1_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
brainpoolP256r1's prime. A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law
`h`, the variant `Variants/BrainpoolP256r1/Arm/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.PointBrainpoolP256r1

open VG.Proof.Weierstrass.Arm.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `lr` in its own working space and keeps `ws` in \
  `r12`, and computes Renes, Costello and Batina's 40 steps by calls of `vg_brainpoolp256r1_mul_mod_p`, \
  `vg_brainpoolp256r1_add_mod_p` and `vg_brainpoolp256r1_sub_mod_p` on fixed offsets of `ws`, `movw` immediates in \
  `r1`–`r3`. It writes no register but `r0`–`r3`, `r12` and `lr`."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  { Spec.Weierstrass.Point.brainpoolp256r1.addApi with
    target := Arm.target
    doc := Spec.Weierstrass.Point.brainpoolp256r1.addApi.doc (notes := notes)
    code := Impl.Weierstrass.Arm.Point.pointAdd Spec.Weierstrass.Point.brainpoolp256r1
    contract := Spec.Weierstrass.Point.brainpoolp256r1.addContract Arm.abi
    verified := brainpoolp256r1_add_verified (fermat_of_law h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Weierstrass.Point.brainpoolp256r1.doubleApi with
    target := Arm.target
    doc := Spec.Weierstrass.Point.brainpoolp256r1.doubleApi.doc (notes := notes)
    code := Impl.Weierstrass.Arm.Point.pointDouble Spec.Weierstrass.Point.brainpoolp256r1
    contract := Spec.Weierstrass.Point.brainpoolp256r1.doubleContract Arm.abi
    verified := brainpoolp256r1_double_verified (fermat_of_law h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.BrainpoolP256r1.Arm.PointBrainpoolP256r1
