module

public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit

/-! # SM4-CFB128 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbEncrypt
    stack := 3264
    verified := Proof.Sm4.AArch64.cfbEncrypt_framed },
  Spec.Sm4.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbDecrypt
    stack := 3264
    verified := Proof.Sm4.AArch64.cfbDecrypt_framed },
  Spec.Sm4.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbEncryptFinal
    stack := 3264
    verified := Proof.Sm4.AArch64.cfbEncryptFinal_framed },
  Spec.Sm4.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbDecryptFinal
    stack := 3264
    verified := Proof.Sm4.AArch64.cfbDecryptFinal_framed }]

end VG.Artifacts.Sm4Cfb.AArch64
