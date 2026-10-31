module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP512r1.Lit

/-!
# ECDH over brainpoolP512r1 (SP 800-56A §5.7.1.2) on PPC64LE

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.PPC64LE.EcdhBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeBrainpoolP512r1
    verified := Proof.Ecdh.PPC64LE.BrainpoolP512r1.ecdh_verified h.law }]

end VG.Generic.BrainpoolP512r1.PPC64LE.EcdhBrainpoolP512r1
