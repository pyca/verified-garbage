module

public import VerifiedGarbage.Proof.Sm4.Arm.Batch32Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-GCM's counter mode on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.Arm

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact Arm.target {
    notes := ["Baseline ARMv7: `vg_sm4_ctr`'s code (the bitsliced round-key table prepared once per message, then up to eight independent counters encrypted per batch) with GCM's `inc₃₂` on the counter: only its last word, byte-reversed, incremented and stored back. The 1512-byte working space is kept on the stack and zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCtr32.ctr32
    stack := 1520
    verified := Proof.Sm4.Arm.Batch32Verified.framed }]

end VG.Artifacts.Sm4Gcm.Arm
