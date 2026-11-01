module

public import VerifiedGarbage.Proof.Sm3.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM3 (GB/T 32905-2016) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm3.Arm

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact Arm.target {
    code := Impl.Sm3.Arm.Stream.init
    verified := Proof.Sm3.Arm.Shared.init },
  Spec.Sm3.updateApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 168 2 Impl.Sm3.Arm.Stream.update
    stack := 168
    verified := Proof.Sm3.Arm.Shared.update },
  Spec.Sm3.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 168 1 Impl.Sm3.Arm.Stream.finalize
    stack := 168
    verified := Proof.Sm3.Arm.Shared.finalize }]

end VG.Artifacts.Sm3.Arm
