module

public import VerifiedGarbage.Proof.Sm4.Arm.CtrVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! # SM4-CTR artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.Arm

def artifacts : List Artifact := [
  { Spec.Sm4.ctrApi with
    target := Arm.target
    doc := Spec.Sm4.ctrApi.doc
      (notes := ["Baseline ARMv7: the generic CTR of `Impl/Modes/Arm/`, one counter block at a time, with full 128-bit big-endian increments, calling the verified `vg_sm4_ecb_encrypt` on the chaining value in a 72-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.ctr
    contract := Spec.Sm4.ctrContract Arm.abi 1560
    stack := 1560
    verified := Proof.Sm4.Arm.ctr_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4Ctr.Arm
