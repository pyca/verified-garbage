module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointP384
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-384's point addition and doubling on PPC64LE

`vg_p384_point_add` and `vg_p384_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
P-384's prime. A generic file (see `TCB/Emit.lean`) over P-384's group law
`h`, the variant `Variants/P384/PPC64LE/Law.lean`, which gives Fermat's
little theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.PointP384

open VG.Proof.Weierstrass.PPC64LE.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `lr` in its own working space and computes Renes, \
  Costello and Batina's 40 steps by calls of `vg_p384_mul_mod_p`, `vg_p384_add_mod_p` and \
  `vg_p384_sub_mod_p` on fixed offsets of `ws` (in `r3`, which they keep), `li` immediates in \
  `r4`–`r6`. It writes no register but `r0`, `r4`–`r12` and `lr`, which it restores."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Weierstrass.Point.p384.addApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd Spec.Weierstrass.Point.p384
    verified := p384_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.p384.doubleApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble Spec.Weierstrass.Point.p384
    verified := p384_double_verified (fermat_of_law h.law) }]

end VG.Generic.P384.PPC64LE.PointP384
