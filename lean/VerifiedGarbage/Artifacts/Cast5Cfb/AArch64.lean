module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # CAST5-CFB64 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbEncrypt
    verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.AArch64.cfbEncrypt_framed },
  Spec.Cast5.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x5 28 Impl.Cast5.AArch64.Tbl.cfbDecrypt
    verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.AArch64.Tbl.cfbDecrypt_framed },
  Spec.Cast5.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbEncryptFinal
    verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.AArch64.cfbEncryptFinal_framed },
  Spec.Cast5.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbDecryptFinal
    verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.AArch64.cfbDecryptFinal_framed }]

end VG.Artifacts.Cast5Cfb.AArch64
