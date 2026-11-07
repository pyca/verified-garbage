module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit

/-! # Triple DES-CFB64 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfbEncrypt
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfbEncrypt_framed },
  Spec.TripleDes.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfbDecrypt
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfbDecrypt_framed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfbEncryptFinal
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfbEncryptFinal_framed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfbDecryptFinal
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfbDecryptFinal_framed }]

end VG.Artifacts.TripleDesCfb.AArch64
