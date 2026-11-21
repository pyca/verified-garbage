module

public import VerifiedGarbage.Impl.Cast5.AArch64.Fn
public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
public import VerifiedGarbage.Proof.Cast5.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # CAST5-CFB64 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cfbEncrypt
    verified := .scrubbed Proof.Cast5.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cfbDecrypt
    verified := .scrubbed Proof.Cast5.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Cast5.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Cast5.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

end VG.Artifacts.Cast5Cfb.AArch64
