module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P384.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384Comb

/-! # ECDSA over P-384 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384.Arm

open VG.Proof.P384.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P384.Scrub.verifyReg hasLaw.law),
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P384.Scrub.verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target (Proof.Ecdsa.Arm.P384.Scrub.signReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target (Proof.Ecdsa.Arm.P384.Scrub.signUReg hasLaw.law)]

end VG.Artifacts.EcdsaP384.Arm
