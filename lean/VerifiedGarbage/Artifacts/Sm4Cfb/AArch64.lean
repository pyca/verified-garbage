module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
public import VerifiedGarbage.Proof.Sm4.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit

/-! # SM4-CFB128 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.cfbEncryptSm4
    verified := Proof.Sm4.AArch64.ModesResidue.cfbEncryptSm4Code_scrubbed },
  Spec.Sm4.cfbEncryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.cfbEncrypt
    verified := Proof.Sm4.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.cfbDecryptSm4
    verified := Proof.Sm4.AArch64.ModesResidue.cfbDecryptSm4Code_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.cfbDecrypt
    verified := Proof.Sm4.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.cfbEncryptFinalSm4
    verified := Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalSm4Code_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.cfbEncryptFinal
    verified := Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.cfbDecryptFinalSm4
    verified := Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalSm4Code_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.cfbDecryptFinal
    verified := Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

end VG.Artifacts.Sm4Cfb.AArch64
