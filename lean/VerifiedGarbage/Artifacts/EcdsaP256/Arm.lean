module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P256.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Comb

/-! # ECDSA over P-256 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP256.Arm

open VG.Proof.P256.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P256.Scrub.verifyReg hasLaw.law),
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P256.Scrub.verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target (Proof.Ecdsa.Arm.P256.Scrub.signReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target (Proof.Ecdsa.Arm.P256.Scrub.signUReg hasLaw.law)]

end VG.Artifacts.EcdsaP256.Arm
