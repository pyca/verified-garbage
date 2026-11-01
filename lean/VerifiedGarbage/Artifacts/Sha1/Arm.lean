module

public import VerifiedGarbage.Proof.Sha1.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-1 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha1.Arm

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact Arm.target {
    code := Impl.Sha1.Arm.Stream.init
    verified := Proof.Sha1.Arm.Shared.init },
  Spec.Sha1.updateApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha1.Arm.Stream.update
    stack := 176
    verified := Proof.Sha1.Arm.Shared.update },
  Spec.Sha1.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha1.Arm.Stream.finalize
    stack := 176
    verified := Proof.Sha1.Arm.Shared.finalize }]

end VG.Artifacts.Sha1.Arm
