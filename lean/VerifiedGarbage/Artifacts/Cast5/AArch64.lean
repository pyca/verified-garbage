module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Cast5.AArch64.Scrub
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
  Spec.Cast5.expandKeyApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.Cast5.AArch64.Tbl.expandKey
    verified := Proof.Cast5.AArch64.Tbl.expandKey_verified }
      ⟨[.x1, .x2, .x4, .x6, .x9, .x10, .x15, .x16, .x17],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
       .v26, .v28, .v29, .v30, .v31],
       []⟩ Proof.Cast5.AArch64.Scrub.expandKeyOk),
  Spec.Cast5.ecbEncryptApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.Tbl.ecbEncryptCleared
    verified := Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_verified
    residue := some ⟨Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_noResidue⟩ },
  Spec.Cast5.ecbDecryptApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.Tbl.ecbDecryptCleared
    verified := Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_verified
    residue := some ⟨Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_noResidue⟩ }]

end VG.Artifacts.Cast5.AArch64
