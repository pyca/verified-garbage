module

public import VerifiedGarbage.Proof.Sm4.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit

/-! # SM4-CFB128 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncrypt
    stack := 3216
    verified := Proof.Sm4.X86_64.cfbEncrypt_framed },
  Spec.Sm4.cfbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecrypt
    stack := 3216
    verified := Proof.Sm4.X86_64.cfbDecrypt_framed }]

end VG.Artifacts.Sm4Cfb.X86_64
