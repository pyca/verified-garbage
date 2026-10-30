module

public import VerifiedGarbage.Proof.Seed.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.AArch64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcEncryptChained
    stack := 1456
    verified := Proof.Seed.AArch64.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcDecryptChained
    stack := 1456
    verified := Proof.Seed.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.AArch64
