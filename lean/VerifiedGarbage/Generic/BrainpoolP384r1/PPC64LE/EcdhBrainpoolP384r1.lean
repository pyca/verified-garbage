module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP384r1.Lit

/-! # ECDH over brainpoolP384r1 (SP 800-56A §5.7.1.2) on PPC64LE -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.PPC64LE.EcdhBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdh.BrainpoolP384r1.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeBrainpoolP384r1
    verified := Proof.Ecdh.PPC64LE.BrainpoolP384r1.ecdh_verified h.law }]

end VG.Generic.BrainpoolP384r1.PPC64LE.EcdhBrainpoolP384r1
