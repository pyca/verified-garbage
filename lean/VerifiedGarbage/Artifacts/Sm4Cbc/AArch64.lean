module

public import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SM4-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 Impl.Sm4.AArch64.Sm4e.cbcEncryptChained
    verified := Proof.Sm4.AArch64.Sm4e.cbcEncryptChained_framed },
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cbcEncryptChained
    verified := Proof.Sm4.AArch64.cbcEncryptChained_framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Sm4.AArch64.Sm4e.cbcDecryptChained
    verified := Proof.Sm4.AArch64.Sm4e.cbcDecryptChained_framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cbcDecryptChained
    verified := Proof.Sm4.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.Sm4Cbc.AArch64
