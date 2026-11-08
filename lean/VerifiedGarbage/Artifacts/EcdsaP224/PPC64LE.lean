module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P224.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P224.Lit
public import VerifiedGarbage.Proof.P224.PPC64LE.Law

/-! # ECDSA signatures over P-224 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224.PPC64LE

open VG.Proof.P224.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyP224
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.P224.verifyHash_verified hasLaw.law }]

end VG.Artifacts.EcdsaP224.PPC64LE
