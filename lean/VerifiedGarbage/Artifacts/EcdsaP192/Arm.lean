module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P192.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P192.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192Comb

/-! # ECDSA over P-192 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP192.Arm

open VG.Proof.P192.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P192.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P192.Scrub.verifyReg hasLaw.law),
  Spec.Ecdsa.P192.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P192.Scrub.verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact Arm.target (Proof.Ecdsa.Arm.P192.Scrub.signReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact Arm.target (Proof.Ecdsa.Arm.P192.Scrub.signUReg hasLaw.law)]

end VG.Artifacts.EcdsaP192.Arm
