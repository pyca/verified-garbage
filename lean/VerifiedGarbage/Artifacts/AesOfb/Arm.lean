module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Spec.Ofb.Final
import VerifiedGarbage.Proof.Aes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OFB (NIST SP 800-38A §6.4) on ARMv7 -/

namespace VG.Artifacts.AesOfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ofb.aesApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ofb
    verified := Proof.Aes.Arm.Fn.ofb },
  Spec.Ofb.aesFinalApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ofbFinal
    verified := Proof.Aes.Arm.Fn.ofbFinal }]

spec_apis artifacts

end VG.Artifacts.AesOfb.Arm
