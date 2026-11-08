module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P384.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.P384.Lit
public import VerifiedGarbage.Proof.P384.PPC64LE.Law

/-! # P-384 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP384.PPC64LE

open VG.Proof.P384.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP384
    verified := Proof.EcKey.PPC64LE.P384.pk_verified hasLaw.law }]

end VG.Artifacts.EcP384.PPC64LE
