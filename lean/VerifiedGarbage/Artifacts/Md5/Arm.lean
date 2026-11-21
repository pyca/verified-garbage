module

public import VerifiedGarbage.Proof.Md5.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # MD5 (RFC 1321) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Md5.Arm

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact Arm.target {
    code := Impl.Md5.Arm.Fn.init
    verified := Proof.Md5.Arm.Fn.init },
  Spec.Md5.updateApi.artifact Arm.target {
    code := Impl.Md5.Arm.Fn.update
    verified := Proof.Md5.Arm.Fn.update },
  Spec.Md5.finalizeApi.artifact Arm.target {
    code := Impl.Md5.Arm.Fn.finalize
    verified := Proof.Md5.Arm.Fn.finalize }]

end VG.Artifacts.Md5.Arm
