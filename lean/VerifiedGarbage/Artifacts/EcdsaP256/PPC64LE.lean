module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Lit
public import VerifiedGarbage.Proof.P256.PPC64LE.Law

/-! # ECDSA over P-256 (FIPS 186-5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaP256.PPC64LE

open VG.Proof.P256.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P256.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifyP256
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.verifyHash_verified hasLaw.law }]

end VG.Artifacts.EcdsaP256.PPC64LE
