module

public import VerifiedGarbage.Proof.AesOcb.Arm.Init
public import VerifiedGarbage.Proof.AesOcb.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-OCB (RFC 7253) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesOcb.Arm

open VG.Proof.AesOcb.Arm

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init
    stack := 2568
    verified := init_framed },
  Spec.Ocb.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«seal»
    stack := 2600
    verified := seal_framed },
  Spec.Ocb.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«open»
    stack := 2600
    verified := open_framed }]

end VG.Artifacts.AesOcb.Arm
