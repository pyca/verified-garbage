module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointBrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP384r1's point addition and doubling on PPC64LE

`vg_brainpoolp384r1_point_add` and `vg_brainpoolp384r1_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
brainpoolP384r1's prime. A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law
`h`, the variant `Variants/BrainpoolP384r1/PPC64LE/Law.lean`, which gives Fermat's
little theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.PPC64LE.PointBrainpoolP384r1

open VG.Proof.Weierstrass.PPC64LE.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Weierstrass.Point.brainpoolp384r1.addApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd Spec.Weierstrass.Point.brainpoolp384r1
    verified := brainpoolp384r1_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.brainpoolp384r1.doubleApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble Spec.Weierstrass.Point.brainpoolp384r1
    verified := brainpoolp384r1_double_verified (fermat_of_law h.law) }]

end VG.Generic.BrainpoolP384r1.PPC64LE.PointBrainpoolP384r1
