module

public import VerifiedGarbage.Proof.Camellia.Arm.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CTR artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CTR mode calls the verified vg_camellia_ecb_encrypt once per counter block. The full 128-bit big-endian counter increment is verified. Its 72-byte working space is kept on the stack and zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ctr
    stack := 2904
    verified := Proof.Camellia.Arm.ctr_framed }]

end VG.Artifacts.CamelliaCtr.Arm
