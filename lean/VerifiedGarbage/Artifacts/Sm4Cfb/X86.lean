module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.FbLit

/-! # SM4-CFB128 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.X86

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbEncrypt
    stack := 1516
    verified := Proof.Sm4.X86.Fb.cfbEncrypt_framed },
  Spec.Sm4.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cfbDecrypt
    stack := 1516
    verified := Proof.Sm4.X86.Fb.cfbDecrypt_framed }]

end VG.Artifacts.Sm4Cfb.X86
