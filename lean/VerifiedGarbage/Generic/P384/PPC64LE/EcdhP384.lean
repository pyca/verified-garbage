module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P384.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P384.Lit

/-!
# ECDH over P-384 (SP 800-56A §5.7.1.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.EcdhP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdh.P384.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeP384
    verified := Proof.Ecdh.PPC64LE.P384.ecdh_verified h.law }]

end VG.Generic.P384.PPC64LE.EcdhP384
