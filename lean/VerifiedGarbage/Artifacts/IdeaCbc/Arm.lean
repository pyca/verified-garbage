module

public import VerifiedGarbage.Proof.Idea.Arm.CbcVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.Arm

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_idea_ecb` (under the encryption subkeys) on each block in a 56-byte working space on the stack, zeroed on return. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcEncryptChained
    stack := 96
    verified := Proof.Idea.Arm.cbcEncryptChained_framed },
  Spec.Idea.cbcDecryptChainedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_idea_ecb` (under the decryption subkeys) on each block in place, with the chaining value in a 56-byte working space on the stack, zeroed on return. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcDecryptChained
    stack := 96
    verified := Proof.Idea.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.IdeaCbc.Arm
