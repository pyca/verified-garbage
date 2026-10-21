module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CTR artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.Arm

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact Arm.target {
    notes := ["Baseline ARMv7: prepare the bitsliced round-key table once per message, then encrypt up to eight independent counters per batch with full 128-bit big-endian increments. The 1512-byte working space is kept on the stack and zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCtr.ctr
    stack := 1520
    verified := Proof.Sm4.Arm.BatchVerified.framed }]

end VG.Artifacts.Sm4Ctr.Arm
