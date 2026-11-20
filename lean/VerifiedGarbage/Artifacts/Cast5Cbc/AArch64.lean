module

public import VerifiedGarbage.Impl.Cast5.AArch64.Fn
public import VerifiedGarbage.Proof.Cast5.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit

/-! # CAST5-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Cast5.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Cast5.AArch64.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Cast5.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.Cast5Cbc.AArch64
