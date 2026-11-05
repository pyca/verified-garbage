module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Lit

/-! # ECDSA signatures over secp256k1 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifySecp256k1
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.Secp256k1.verifyHash_verified h.law }]

end VG.Generic.Secp256k1.PPC64LE.EcdsaSecp256k1
