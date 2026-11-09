module

public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalLit

/-! # IDEA-CFB64 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.AArch64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbEncrypt
    stack := 208
    verified := Proof.Idea.AArch64.cfbEncrypt_framed },
  Spec.Idea.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbDecrypt
    stack := 208
    verified := Proof.Idea.AArch64.cfbDecrypt_framed },
  Spec.Idea.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbEncryptFinal
    stack := 208
    verified := Proof.Idea.AArch64.cfbEncryptFinal_framed },
  Spec.Idea.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbDecryptFinal
    stack := 208
    verified := Proof.Idea.AArch64.cfbDecryptFinal_framed }]

end VG.Artifacts.IdeaCfb.AArch64
