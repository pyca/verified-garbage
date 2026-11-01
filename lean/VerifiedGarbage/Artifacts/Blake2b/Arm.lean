module

public import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
public import VerifiedGarbage.Proof.Blake2.Arm.CompressB
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2b (RFC 7693) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.Arm

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.ArmB.initB_verified },
  Spec.Blake2.updateBApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 592 2 (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
    stack := 16 + 592
    verified := Proof.Blake2.ArmB.updateB_framed },
  Spec.Blake2.finalizeBApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 592 1 (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
    stack := 16 + 592
    verified := Proof.Blake2.ArmB.finalizeB_framed }]

end VG.Artifacts.Blake2b.Arm
