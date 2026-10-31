module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P224.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.Lit

/-! # P-224 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.EcP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP224
    verified := Proof.EcKey.PPC64LE.P224.pk_verified h.law }]

end VG.Generic.P224.PPC64LE.EcP224
