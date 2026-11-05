module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Impl.Ecdsa.Verify.P192.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Lit

/-! # ECDSA signatures over P-192 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P192.PPC64LE.EcdsaP192

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.Ecdsa.P192.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyP192
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.P192.verifyHash_verified h.law }]

end VG.Generic.P192.PPC64LE.EcdsaP192
