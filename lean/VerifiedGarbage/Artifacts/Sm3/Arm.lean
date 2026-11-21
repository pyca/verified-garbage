module

public import VerifiedGarbage.Proof.Sm3.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM3 (GB/T 32905-2016) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm3.Arm

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact Arm.target {
    code := Impl.Sm3.Arm.Fn.init
    verified := Proof.Sm3.Arm.Fn.init },
  Spec.Sm3.updateApi.artifact Arm.target {
    code := Impl.Sm3.Arm.Fn.update
    verified := Proof.Sm3.Arm.Fn.update },
  Spec.Sm3.finalizeApi.artifact Arm.target {
    code := Impl.Sm3.Arm.Fn.finalize
    verified := Proof.Sm3.Arm.Fn.finalize }]

end VG.Artifacts.Sm3.Arm
