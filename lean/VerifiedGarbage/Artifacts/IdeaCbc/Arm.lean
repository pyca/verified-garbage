module

public import VerifiedGarbage.Proof.Idea.Arm.CbcVerified
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Impl.Aes.Arm.Alloc
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.Arm

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_idea_ecb` (under the encryption subkeys) on each block in a 56-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcEncrypt
    stack := 96
    verified := Proof.Idea.Arm.cbcEncrypt_framed },
  Spec.Idea.cbcDecryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_idea_ecb` (under the decryption subkeys) on each block in place, with the chaining value in a 56-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcDecrypt
    stack := 96
    verified := Proof.Idea.Arm.cbcDecrypt_framed }]

end VG.Artifacts.IdeaCbc.Arm
