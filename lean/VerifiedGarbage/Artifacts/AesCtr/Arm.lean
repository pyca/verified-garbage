module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Ctr.Final
import VerifiedGarbage.Proof.Aes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CTR (NIST SP 800-38A §6.5) on ARMv7 -/

namespace VG.Artifacts.AesCtr.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ctr.aesApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ctr
    verified := Proof.Aes.Arm.Fn.ctr },
  Spec.Ctr.aesFinalApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ctrFinal
    verified := Proof.Aes.Arm.Fn.ctrFinal }]

spec_apis artifacts

end VG.Artifacts.AesCtr.Arm
