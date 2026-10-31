module

public import VerifiedGarbage.Proof.Idea.Arm.FbVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CFB64 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.Arm

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbEncrypt
    stack := 96
    verified := Proof.Idea.Arm.cfbEncrypt_framed },
  Spec.Idea.cfbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbDecrypt
    stack := 96
    verified := Proof.Idea.Arm.cfbDecrypt_framed }]

end VG.Artifacts.IdeaCfb.Arm
