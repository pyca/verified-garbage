module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CMAC (NIST SP 800-38B) on ARMv7 -/

namespace VG.Artifacts.CmacAes.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cmac.aesInitApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.Fn.init
    verified := Proof.CmacAes.Arm.Fn.init },
  Spec.Cmac.aesAbsorbApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.Fn.absorb
    verified := Proof.CmacAes.Arm.Fn.absorb },
  Spec.Cmac.aesFinishApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.Fn.finish
    verified := Proof.CmacAes.Arm.Fn.finish }]

spec_apis artifacts

end VG.Artifacts.CmacAes.Arm
