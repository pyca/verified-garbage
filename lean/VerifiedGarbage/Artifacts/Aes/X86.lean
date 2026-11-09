module
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
public import VerifiedGarbage.Proof.Aes.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print


/-! # AES (FIPS 197) on x86 -/

@[expose] public section

namespace VG.Artifacts.Aes.X86

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey
    stack := 532
    verified := Proof.Aes.X86.scalar_expandKey_framed },
  Spec.Aes.expandKeyApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey
    stack := 532
    verified := Proof.Aes.X86.aesni_expandKey_framed }]

end VG.Artifacts.Aes.X86
