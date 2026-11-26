module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SHA-1 (FIPS 180-4) on ARMv7 -/

namespace VG.Artifacts.Sha1.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Sha1.initApi.artifact Arm.target {
    code := Impl.Sha1.Arm.Fn.init
    verified := Proof.Sha1.Arm.Fn.init },
  Spec.Sha1.updateApi.artifact Arm.target {
    code := Impl.Sha1.Arm.Fn.update
    verified := Proof.Sha1.Arm.Fn.update },
  Spec.Sha1.finalizeApi.artifact Arm.target {
    code := Impl.Sha1.Arm.Fn.finalize
    verified := Proof.Sha1.Arm.Fn.finalize },
  Spec.Sha1.digestApi.artifact Arm.target {
    code := Impl.Sha1.Arm.Fn.digest
    verified := Proof.Sha1.Arm.Fn.digest }]

spec_apis artifacts

end VG.Artifacts.Sha1.Arm
