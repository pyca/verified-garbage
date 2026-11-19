module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
public import VerifiedGarbage.Proof.Sm4.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
import VerifiedGarbage.Proof.Sm4.X86.FbLit

/-! # SM4-CFB128 on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.X86

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncrypt
    verified := .unscrubbed Proof.Sm4.X86.Fb.cfbEncrypt_framed },
  Spec.Sm4.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecrypt
    verified := .unscrubbed Proof.Sm4.X86.Fb.cfbDecrypt_framed },
  Spec.Sm4.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncryptFinal
    verified := .unscrubbed Proof.Sm4.X86.FbFinal.cfbEncryptFinal_framed },
  Spec.Sm4.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecryptFinal
    verified := .unscrubbed Proof.Sm4.X86.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.Sm4Cfb.X86
