module

public import VerifiedGarbage.Proof.CmacAes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CMAC (NIST SP 800-38B) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CmacAes.Arm

def artifacts : List Artifact := [
  Spec.Cmac.aesInitApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.Fn.init
    verified := Proof.CmacAes.Arm.Fn.init },
  Spec.Cmac.aesAbsorbApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.Fn.absorb
    verified := Proof.CmacAes.Arm.Fn.absorb },
  Spec.Cmac.aesFinishApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.Fn.finish
    verified := Proof.CmacAes.Arm.Fn.finish }]

end VG.Artifacts.CmacAes.Arm
