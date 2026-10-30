module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P521.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P521.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P521.Lit

/-!
# ECDH over P-521 (SP 800-56A §5.7.1.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.EcdhP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeP521
    verified := Proof.Ecdh.PPC64LE.P521.ecdh_verified h.law }]

end VG.Generic.P521.PPC64LE.EcdhP521
