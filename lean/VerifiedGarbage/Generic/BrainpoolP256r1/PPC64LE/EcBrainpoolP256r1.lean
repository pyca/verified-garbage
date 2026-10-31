module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP256r1.Lit

/-!
# brainpoolP256r1 public keys (FIPS 186-5 §A.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law `h`, the variant
`Variants/BrainpoolP256r1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.PPC64LE.EcBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyBrainpoolP256r1
    verified := Proof.EcKey.PPC64LE.BrainpoolP256r1.pk_verified h.law }]

end VG.Generic.BrainpoolP256r1.PPC64LE.EcBrainpoolP256r1
