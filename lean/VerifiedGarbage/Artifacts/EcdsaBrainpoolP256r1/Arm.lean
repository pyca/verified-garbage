module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmFn
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Comb

/-! # ECDSA over brainpoolP256r1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP256r1.Arm

open VG.Proof.BrainpoolP256r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.Fn.verifyBrainpoolP256r1
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.verifyBrainpoolP256r1 hasLaw.law) },
  Spec.Ecdsa.BrainpoolP256r1.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.Fn.verifyBrainpoolP256r1U
    verified := .scrubbed (Proof.Ecdsa.Arm.Fn.verifyBrainpoolP256r1U hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact Arm.target (Proof.Ecdsa.Arm.BrainpoolP256r1.Scrub.signReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact Arm.target (Proof.Ecdsa.Arm.BrainpoolP256r1.Scrub.signUReg hasLaw.law)]

end VG.Artifacts.EcdsaBrainpoolP256r1.Arm
