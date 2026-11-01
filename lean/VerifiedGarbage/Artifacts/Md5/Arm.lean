module

public import VerifiedGarbage.Proof.Md5.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # MD5 (RFC 1321) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Md5.Arm

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact Arm.target {
    code := Impl.Md5.Arm.Stream.init
    verified := Proof.Md5.Arm.Shared.init },
  Spec.Md5.updateApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update
    stack := 128
    verified := Proof.Md5.Arm.Shared.update },
  Spec.Md5.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 128 1 Impl.Md5.Arm.Stream.finalize
    stack := 128
    verified := Proof.Md5.Arm.Shared.finalize }]

end VG.Artifacts.Md5.Arm
