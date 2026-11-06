module

public import VerifiedGarbage.Proof.Idea.X86_64.FbVerified
public import VerifiedGarbage.Proof.Idea.X86_64.CfbFinalCT
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Idea.X86_64.CfbFinalLit

/-! # IDEA-CFB64 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.X86_64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbEncrypt
    stack := 184
    verified := Proof.Idea.X86_64.cfbEncrypt_framed },
  Spec.Idea.cfbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbDecrypt
    stack := 184
    verified := Proof.Idea.X86_64.cfbDecrypt_framed },
  Spec.Idea.cfbEncryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbEncryptFinal
    stack := 264
    verified := Proof.Idea.X86_64.cfbEncryptFinal_framed },
  Spec.Idea.cfbDecryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbDecryptFinal
    stack := 264
    verified := Proof.Idea.X86_64.cfbDecryptFinal_framed }]

end VG.Artifacts.IdeaCfb.X86_64
