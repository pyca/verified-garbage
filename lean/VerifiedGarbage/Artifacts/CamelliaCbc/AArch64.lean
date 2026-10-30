module

public import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cbcEncryptChained
    stack := 3344
    verified := Proof.Camellia.AArch64.cbcEncryptChained_framed },
  Spec.Camellia.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cbcDecryptChained
    stack := 3344
    verified := Proof.Camellia.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.CamelliaCbc.AArch64
