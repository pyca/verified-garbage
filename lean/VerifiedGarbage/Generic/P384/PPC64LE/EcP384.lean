module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P384.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.EcKey.PPC64LE.P384.Lit

/-! # P-384 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.EcP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP384
    verified := Proof.EcKey.PPC64LE.P384.pk_verified h.law }]

end VG.Generic.P384.PPC64LE.EcP384
