module

public import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cbcEncryptChained
    stack := 3264
    verified := Proof.Sm4.AArch64.cbcEncryptChained_framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cbcDecryptChained
    stack := 3264
    verified := Proof.Sm4.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.Sm4Cbc.AArch64
