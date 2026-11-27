module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Impl.Cast5.AArch64.Fn
import VerifiedGarbage.Proof.Cast5.AArch64.CbcVerified
import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
import VerifiedGarbage.Proof.Cast5.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CBC on AArch64 -/

namespace VG.Artifacts.Cast5Cbc.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Cast5.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cbcEncryptChained
    verified := Proof.Cast5.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cbcDecryptChained
    verified := Proof.Cast5.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Cbc.AArch64
