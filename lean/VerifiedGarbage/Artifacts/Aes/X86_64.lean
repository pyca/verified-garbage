module

public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Frame
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES (FIPS 197) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Aes.X86_64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact X86_64.target {
    suffix := "_aesni"
    code := Impl.Aes.X86_64.AesNi.expandKey
    verified := Proof.Aes.X86_64.AesNi.Key.expandKey3_verified },
  Spec.Aes.expandKeyApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.Aes.X86_64.expandKey
    stack := 520
    verified := Proof.Aes.X86_64.scalar_expandKey_framed }]

end VG.Artifacts.Aes.X86_64
