module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP256r1.Lit
public import VerifiedGarbage.Proof.BrainpoolP256r1.PPC64LE.Law

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP256r1.PPC64LE

open VG.Proof.BrainpoolP256r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyBrainpoolP256r1
    verified := Proof.EcKey.PPC64LE.BrainpoolP256r1.pk_verified hasLaw.law }]

end VG.Artifacts.EcBrainpoolP256r1.PPC64LE
