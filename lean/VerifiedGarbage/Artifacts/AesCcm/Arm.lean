module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.AesCcm.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CCM (NIST SP 800-38C) on ARMv7 -/

namespace VG.Artifacts.AesCcm.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ccm.sealApi.artifact Arm.target {
    code := Impl.AesCcm.Arm.Fn.«seal»
    verified := Proof.AesCcm.Arm.Fn.«seal» },
  Spec.Ccm.openApi.artifact Arm.target {
    code := Impl.AesCcm.Arm.Fn.«open»
    verified := Proof.AesCcm.Arm.Fn.«open» }]

spec_apis artifacts

end VG.Artifacts.AesCcm.Arm
