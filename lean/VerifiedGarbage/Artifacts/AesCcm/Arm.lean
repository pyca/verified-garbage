module

public import VerifiedGarbage.Proof.AesCcm.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CCM (NIST SP 800-38C) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCcm.Arm

open VG.Proof.AesCcm.Arm

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«seal»
    stack := 2608
    verified := seal_framed },
  Spec.Ccm.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«open»
    stack := 2608
    verified := open_framed }]

end VG.Artifacts.AesCcm.Arm
