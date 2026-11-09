module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit

/-! # Blowfish-CFB64 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncrypt
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbEncrypt_framed },
  Spec.Blowfish.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecrypt
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbDecrypt_framed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncryptFinal
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbEncryptFinal_framed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecryptFinal
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbDecryptFinal_framed }]

end VG.Artifacts.BlowfishCfb.AArch64
