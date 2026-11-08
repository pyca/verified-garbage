module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P256.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.Lit
public import VerifiedGarbage.Proof.P256.PPC64LE.Law

/-! # P-256 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP256.PPC64LE

open VG.Proof.P256.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP256
    verified := Proof.EcKey.PPC64LE.pk_verified hasLaw.law }]

end VG.Artifacts.EcP256.PPC64LE
