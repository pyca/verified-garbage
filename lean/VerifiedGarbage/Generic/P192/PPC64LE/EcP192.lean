module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P192.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.EcKey.PPC64LE.P192.Lit

/-! # P-192 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P192.PPC64LE.EcP192

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.EcKey.P192.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP192
    verified := Proof.EcKey.PPC64LE.P192.pk_verified h.law }]

end VG.Generic.P192.PPC64LE.EcP192
