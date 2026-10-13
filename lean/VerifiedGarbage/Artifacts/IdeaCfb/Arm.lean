module

public import VerifiedGarbage.Proof.Idea.Arm.FbVerified
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Impl.Aes.Arm.Alloc

/-! # IDEA-CFB64 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_idea_ecb` on the chaining value in a 56-byte working space on the \
  stack, zeroed on return."

def artifacts : List Artifact := [
  { Spec.Idea.cfbEncryptApi with
    target := Arm.target
    doc := Spec.Idea.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbEncrypt
    contract := Spec.Idea.cfbEncryptContract Arm.abi 96
    stack := 96
    verified := Proof.Idea.Arm.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Idea.cfbDecryptApi with
    target := Arm.target
    doc := Spec.Idea.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbDecrypt
    contract := Spec.Idea.cfbDecryptContract Arm.abi 96
    stack := 96
    verified := Proof.Idea.Arm.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.IdeaCfb.Arm
