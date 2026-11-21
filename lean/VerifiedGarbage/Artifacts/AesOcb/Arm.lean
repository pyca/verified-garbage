module

public import VerifiedGarbage.Proof.AesOcb.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-OCB (RFC 7253) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesOcb.Arm

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact Arm.target {
    code := Impl.AesOcb.Arm.Fn.init
    verified := Proof.AesOcb.Arm.Fn.init },
  Spec.Ocb.sealApi.artifact Arm.target {
    code := Impl.AesOcb.Arm.Fn.«seal»
    verified := Proof.AesOcb.Arm.Fn.«seal» },
  Spec.Ocb.openApi.artifact Arm.target {
    code := Impl.AesOcb.Arm.Fn.«open»
    verified := Proof.AesOcb.Arm.Fn.«open» }]

end VG.Artifacts.AesOcb.Arm
