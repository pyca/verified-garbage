module

public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-1 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha1.Arm

def artifacts : List Artifact := [
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

end VG.Artifacts.Sha1.Arm
