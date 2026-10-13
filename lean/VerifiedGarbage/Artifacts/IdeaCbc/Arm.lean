module

public import VerifiedGarbage.Proof.Idea.Arm.CbcVerified
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Impl.Aes.Arm.Alloc

/-! # IDEA-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.Arm

def artifacts : List Artifact := [
  { Spec.Idea.cbcEncryptApi with
    target := Arm.target
    doc := Spec.Idea.cbcEncryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_idea_ecb` (under the encryption subkeys) on each block in a 56-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcEncrypt
    contract := Spec.Idea.cbcEncryptContract Arm.abi 96
    stack := 96
    verified := Proof.Idea.Arm.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Idea.cbcDecryptApi with
    target := Arm.target
    doc := Spec.Idea.cbcDecryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_idea_ecb` (under the decryption subkeys) on each block in place, with the chaining value in a 56-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcDecrypt
    contract := Spec.Idea.cbcDecryptContract Arm.abi 96
    stack := 96
    verified := Proof.Idea.Arm.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.IdeaCbc.Arm
