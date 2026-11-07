module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit

/-! # Camellia-CFB128 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbEncrypt
    stack := 3344
    verified := Proof.Camellia.AArch64.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbDecrypt
    stack := 3344
    verified := Proof.Camellia.AArch64.cfbDecrypt_framed },
  Spec.Camellia.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbEncryptFinal
    stack := 3344
    verified := Proof.Camellia.AArch64.cfbEncryptFinal_framed },
  Spec.Camellia.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbDecryptFinal
    stack := 3344
    verified := Proof.Camellia.AArch64.cfbDecryptFinal_framed }]

end VG.Artifacts.CamelliaCfb.AArch64
