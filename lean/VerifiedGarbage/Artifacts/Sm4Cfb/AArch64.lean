module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
import VerifiedGarbage.Impl.Sm4.AArch64.Fn
import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
import VerifiedGarbage.Proof.Sm4.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CFB128 on AArch64 -/

namespace VG.Artifacts.Sm4Cfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
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

spec_apis artifacts

end VG.Artifacts.Sm4Cfb.AArch64
