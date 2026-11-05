module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Lit

/-! # ECDSA signatures over P-521 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.EcdsaP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Verify.PPC64LE.verifyP521
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.P521.verifyHash_verified h.law }]

end VG.Generic.P521.PPC64LE.EcdsaP521
