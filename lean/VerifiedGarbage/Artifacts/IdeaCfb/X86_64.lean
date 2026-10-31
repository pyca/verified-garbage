module

public import VerifiedGarbage.Proof.Idea.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit

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
    verified := Proof.Idea.X86_64.cfbDecrypt_framed }]

end VG.Artifacts.IdeaCfb.X86_64
