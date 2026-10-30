module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointP256
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-256's point addition and doubling on PPC64LE

`vg_p256_point_add` and `vg_p256_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
P-256's prime. A generic file (see `TCB/Emit.lean`) over P-256's group law
`h`, the variant `Variants/P256/PPC64LE/Law.lean`, which gives Fermat's
little theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.PointP256

open VG.Proof.Weierstrass.PPC64LE.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Weierstrass.Point.p256.addApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd Spec.Weierstrass.Point.p256
    verified := p256_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.p256.doubleApi.artifact PPC64LE.target {
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble Spec.Weierstrass.Point.p256
    verified := p256_double_verified (fermat_of_law h.law) }]

end VG.Generic.P256.PPC64LE.PointP256
