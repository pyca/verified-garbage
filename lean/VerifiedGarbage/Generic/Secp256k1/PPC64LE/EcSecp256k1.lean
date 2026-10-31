module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.EcKey.PPC64LE.Secp256k1.Lit

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeySecp256k1
    verified := Proof.EcKey.PPC64LE.Secp256k1.pk_verified h.law }]

end VG.Generic.Secp256k1.PPC64LE.EcSecp256k1
