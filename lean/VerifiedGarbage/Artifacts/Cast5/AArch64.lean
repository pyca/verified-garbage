module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Impl.Cast5.AArch64.Fn
import VerifiedGarbage.Proof.Cast5.AArch64.Scrub
import VerifiedGarbage.Proof.Cast5.AArch64.Residue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5 (RFC 2144) on AArch64 -/

namespace VG.Artifacts.Cast5.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Cast5.expandKeyApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Tbl.Fn.expandKey
    verified := Proof.Cast5.AArch64.Scrub.expandKey },
  Spec.Cast5.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.ecbEncrypt
    verified := Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.ecbDecrypt
    verified := Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5.AArch64
