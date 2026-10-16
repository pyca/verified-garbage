module

public import VerifiedGarbage.Proof.Camellia.Arm.CtrVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! # Camellia-CTR artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.Arm

def artifacts : List Artifact := [
  { Spec.Camellia.ctrApi with
    target := Arm.target
    doc := Spec.Camellia.ctrApi.doc
      (notes := ["Baseline ARMv7: the generic CTR mode calls the verified vg_camellia_ecb_encrypt once per counter block. The full 128-bit big-endian counter increment is verified. Its 72-byte working space is kept on the stack and zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ctr
    contract := Spec.Camellia.ctrContract Arm.abi 2904
    stack := 2904
    verified := Proof.Camellia.Arm.ctr_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CamelliaCtr.Arm
