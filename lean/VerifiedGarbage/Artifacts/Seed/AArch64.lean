module

public import VerifiedGarbage.Proof.Seed.AArch64.Frame
public import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Seed.AArch64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 976 .x2 122 Impl.Seed.AArch64.expandKey
    stack := 976
    verified := Proof.Seed.AArch64.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1088 .x3 136 (Impl.Seed.AArch64.ecbCall .encrypt)
    stack := 1104
    verified := Proof.Seed.AArch64.ecbCall_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1088 .x3 136 (Impl.Seed.AArch64.ecbCall .decrypt)
    stack := 1104
    verified := Proof.Seed.AArch64.ecbCall_framed .decrypt }]

end VG.Artifacts.Seed.AArch64
