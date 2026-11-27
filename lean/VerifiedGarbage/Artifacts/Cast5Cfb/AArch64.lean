module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
import VerifiedGarbage.Impl.Cast5.AArch64.Fn
import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Cast5.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CFB64 on AArch64 -/

namespace VG.Artifacts.Cast5Cfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Cast5.cfbEncryptApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cfbEncrypt
    verified := Proof.Cast5.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cfbDecrypt
    verified := Proof.Cast5.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cfbEncryptFinal
    verified := Proof.Cast5.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cfbDecryptFinal
    verified := Proof.Cast5.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Cfb.AArch64
