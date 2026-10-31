module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Secp256k1.Lit

/-! # ECDH over secp256k1 (SP 800-56A §5.7.1.2) on PPC64LE -/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcdhSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeSecp256k1
    verified := Proof.Ecdh.PPC64LE.Secp256k1.ecdh_verified h.law }]

end VG.Generic.Secp256k1.PPC64LE.EcdhSecp256k1
