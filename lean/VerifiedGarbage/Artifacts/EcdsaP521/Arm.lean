module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P521.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P521.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521Comb

/-! # ECDSA over P-521 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP521.Arm

open VG.Proof.P521.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P521.Scrub.verifyReg hasLaw.law),
  Spec.Ecdsa.P521.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P521.Scrub.verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target (Proof.Ecdsa.Arm.P521.Scrub.signReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target (Proof.Ecdsa.Arm.P521.Scrub.signUReg hasLaw.law)]

end VG.Artifacts.EcdsaP521.Arm
