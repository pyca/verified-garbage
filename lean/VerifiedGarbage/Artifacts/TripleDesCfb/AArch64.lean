module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit
public import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCfb

/-! # Triple DES-CFB64 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.cfbEncrypt
    verified := Proof.TripleDes.AArch64.cfbEncrypt_framed },
  Spec.TripleDes.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1120 .x4 140
      Impl.TripleDes.AArch64.Short.cfb64Decrypt
    verified := Proof.TripleDes.AArch64.Short.Cbc.Cfb.cfb64Decrypt_framed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.cfbEncryptFinal
    verified := Proof.TripleDes.AArch64.cfbEncryptFinal_framed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.cfbDecryptFinal
    verified := Proof.TripleDes.AArch64.cfbDecryptFinal_framed }]

end VG.Artifacts.TripleDesCfb.AArch64
