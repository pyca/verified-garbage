module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointBrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP256r1's point addition and doubling on PPC64LE

`vg_brainpoolp256r1_point_add` and `vg_brainpoolp256r1_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
brainpoolP256r1's prime. A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law
`h`, the variant `Variants/BrainpoolP256r1/PPC64LE/Law.lean`, which gives Fermat's
little theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.PPC64LE.PointBrainpoolP256r1

open VG.Proof.Weierstrass.PPC64LE.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `lr` in its own working space and computes Renes, \
  Costello and Batina's 40 steps by calls of `vg_brainpoolp256r1_mul_mod_p`, `vg_brainpoolp256r1_add_mod_p` and \
  `vg_brainpoolp256r1_sub_mod_p` on fixed offsets of `ws` (in `r3`, which they keep), `li` immediates in \
  `r4`–`r6`. It writes no register but `r0`, `r4`–`r12` and `lr`, which it restores."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Weierstrass.Point.brainpoolp256r1.addApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd Spec.Weierstrass.Point.brainpoolp256r1
    verified := brainpoolp256r1_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.brainpoolp256r1.doubleApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble Spec.Weierstrass.Point.brainpoolp256r1
    verified := brainpoolp256r1_double_verified (fermat_of_law h.law) }]

end VG.Generic.BrainpoolP256r1.PPC64LE.PointBrainpoolP256r1
