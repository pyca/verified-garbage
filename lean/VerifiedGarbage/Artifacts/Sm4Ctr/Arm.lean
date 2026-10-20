module

public import VerifiedGarbage.Proof.Sm4.Arm.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CTR artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.Arm

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CTR of `Impl/Modes/Arm/`, one counter block at a time, with full 128-bit big-endian increments, calling the verified `vg_sm4_ecb_encrypt` on the chaining value in a 72-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.ctr
    stack := 1560
    verified := Proof.Sm4.Arm.ctr_framed }]

end VG.Artifacts.Sm4Ctr.Arm
