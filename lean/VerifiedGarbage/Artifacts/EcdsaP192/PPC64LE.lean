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
public import VerifiedGarbage.Proof.P192.PPC64LE.Law

/-! # ECDSA signatures over P-192 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaP192.PPC64LE

open VG.Proof.P192.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P192.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyP192
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.P192.verifyHash_verified hasLaw.law }]

end VG.Artifacts.EcdsaP192.PPC64LE
