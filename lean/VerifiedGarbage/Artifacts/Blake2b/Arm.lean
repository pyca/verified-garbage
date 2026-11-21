module

public import VerifiedGarbage.Proof.Blake2.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # BLAKE2b (RFC 7693) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.Arm

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.initB
    verified := Proof.Blake2.Arm.Fn.initB },
  Spec.Blake2.updateBApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.updateB
    verified := Proof.Blake2.Arm.Fn.updateB },
  Spec.Blake2.finalizeBApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.finalizeB
    verified := Proof.Blake2.Arm.Fn.finalizeB }]

end VG.Artifacts.Blake2b.Arm
