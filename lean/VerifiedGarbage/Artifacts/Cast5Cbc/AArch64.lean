module

public import VerifiedGarbage.Proof.Cast5.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact AArch64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cbcEncryptChained
    stack := 112
    verified := Proof.Cast5.AArch64.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact AArch64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cbcDecryptChained
    stack := 112
    verified := Proof.Cast5.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.AArch64
