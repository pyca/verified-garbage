module

public import VerifiedGarbage.Proof.Cast5.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit

/-! # CAST5-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cbcEncryptChained
    verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.AArch64.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x5 28 Impl.Cast5.AArch64.Tbl.cbcDecryptChained
    verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.AArch64.Tbl.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.AArch64
