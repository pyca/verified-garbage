module

public import VerifiedGarbage.Proof.Idea.Arm.FbVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CFB64 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_idea_ecb` on the chaining value in a 56-byte working space on the \
  stack, zeroed on return."

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbEncrypt
    stack := 96
    verified := Proof.Idea.Arm.cfbEncrypt_framed },
  Spec.Idea.cfbDecryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbDecrypt
    stack := 96
    verified := Proof.Idea.Arm.cfbDecrypt_framed }]

end VG.Artifacts.IdeaCfb.Arm
