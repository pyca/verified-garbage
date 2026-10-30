module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P521.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P521.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.EcKey.PPC64LE.P521.Lit

/-!
# P-521 public keys (FIPS 186-5 §A.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.EcP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.EcKey.P521.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP521
    verified := Proof.EcKey.PPC64LE.P521.pk_verified h.law }]

end VG.Generic.P521.PPC64LE.EcP521
