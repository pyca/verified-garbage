module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Lit

/-! # ECDSA signatures over P-384 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.EcdsaP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyP384
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.P384.verifyHash_verified h.law }]

end VG.Generic.P384.PPC64LE.EcdsaP384
