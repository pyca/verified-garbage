module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblEcbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.TblKey
public import VerifiedGarbage.Proof.Cast5.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit

/-! # CAST5 (RFC 2144) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Tbl.expandKey
    verified := Proof.Cast5.AArch64.Tbl.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.Tbl.ecbEncryptCleared
    verified := Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_verified
    residue := some ⟨Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_noResidue⟩ },
  Spec.Cast5.ecbDecryptApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.Tbl.ecbDecryptCleared
    verified := Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_verified
    residue := some ⟨Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_noResidue⟩ }]

end VG.Artifacts.Cast5.AArch64
