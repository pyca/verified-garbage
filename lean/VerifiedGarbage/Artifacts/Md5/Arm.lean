module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Md5.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # MD5 (RFC 1321) on ARMv7 -/

namespace VG.Artifacts.Md5.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Md5.initApi.artifact Arm.target {
    code := Impl.Md5.Arm.Fn.init
    verified := Proof.Md5.Arm.Fn.init },
  Spec.Md5.updateApi.artifact Arm.target {
    code := Impl.Md5.Arm.Fn.update
    verified := Proof.Md5.Arm.Fn.update },
  Spec.Md5.finalizeApi.artifact Arm.target {
    code := Impl.Md5.Arm.Fn.finalize
    verified := Proof.Md5.Arm.Fn.finalize }]

spec_apis artifacts

end VG.Artifacts.Md5.Arm
