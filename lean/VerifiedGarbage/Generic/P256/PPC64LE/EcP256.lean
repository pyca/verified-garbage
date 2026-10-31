module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P256.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.EcKey.PPC64LE.Lit

/-! # P-256 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.EcP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP256
    verified := Proof.EcKey.PPC64LE.pk_verified h.law }]

end VG.Generic.P256.PPC64LE.EcP256
