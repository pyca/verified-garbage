module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointSecp256k1
public import VerifiedGarbage.Impl.Secp256k1.Point
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# secp256k1's point addition and doubling on PPC64LE

`vg_secp256k1_point_add` and `vg_secp256k1_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
secp256k1's prime. A generic file (see `TCB/Emit.lean`) over secp256k1's group law
`h`, the variant `Variants/Secp256k1/PPC64LE/Law.lean`, which gives Fermat's
little theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.PointSecp256k1

open VG.Proof.Weierstrass.PPC64LE.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `lr` in its own working space and computes Renes, \
  Costello and Batina's 40 steps by calls of `vg_secp256k1_mul_mod_p`, `vg_secp256k1_add_mod_p` and \
  `vg_secp256k1_sub_mod_p` on fixed offsets of `ws` (in `r3`, which they keep), `li` immediates in \
  `r4`–`r6`. It writes no register but `r0`, `r4`–`r12` and `lr`, which it restores."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Impl.Secp256k1.point.addApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.Weierstrass.PPC64LE.Point.pointAdd Impl.Secp256k1.point
    verified := secp256k1_add_verified (fermat_of_law h.law) },
  Impl.Secp256k1.point.doubleApi.artifact PPC64LE.target {
    notes := notes
    code := Impl.Weierstrass.PPC64LE.Point.pointDouble Impl.Secp256k1.point
    verified := secp256k1_double_verified (fermat_of_law h.law) }]

end VG.Generic.Secp256k1.PPC64LE.PointSecp256k1
