module

public import VerifiedGarbage.Proof.Cast5.AArch64.Scrub
public import VerifiedGarbage.Proof.Cast5.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit

/-! # CAST5 (RFC 2144) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Tbl.Fn.expandKey
    verified := .scrubbed Proof.Cast5.AArch64.Scrub.expandKey },
  Spec.Cast5.ecbEncryptApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.Tbl.ecbEncryptCleared
    verified := .scrubbed Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.Tbl.ecbDecryptCleared
    verified := .scrubbed Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_scrubbed }]

end VG.Artifacts.Cast5.AArch64
