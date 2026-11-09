module

public import VerifiedGarbage.Proof.Idea.X86.FbVerified
public import VerifiedGarbage.Proof.Idea.X86.FbFinalVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit

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
    verified := Proof.Idea.X86.Fb.cfbDecrypt_framed },
  Spec.Idea.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbEncryptFinal
    stack := 208
    verified := Proof.Idea.X86.FbFinal.cfbEncryptFinal_framed },
  Spec.Idea.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbDecryptFinal
    stack := 208
    verified := Proof.Idea.X86.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.IdeaCfb.X86
