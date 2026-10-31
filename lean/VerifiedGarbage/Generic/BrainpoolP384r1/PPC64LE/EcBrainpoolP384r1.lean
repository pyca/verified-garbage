module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP384r1.Lit

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.PPC64LE.EcBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyBrainpoolP384r1
    verified := Proof.EcKey.PPC64LE.BrainpoolP384r1.pk_verified h.law }]

end VG.Generic.BrainpoolP384r1.PPC64LE.EcBrainpoolP384r1
