module

public import VerifiedGarbage.Proof.Idea.X86.FbVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86.ModesLit

/-! # IDEA-CFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.X86

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbEncrypt
    stack := 208
    verified := Proof.Idea.X86.Fb.cfbEncrypt_framed },
  Spec.Idea.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbDecrypt
    stack := 208
    verified := Proof.Idea.X86.Fb.cfbDecrypt_framed }]

end VG.Artifacts.IdeaCfb.X86
