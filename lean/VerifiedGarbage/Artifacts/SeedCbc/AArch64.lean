module

public import VerifiedGarbage.Impl.Seed.AArch64.Fn
public import VerifiedGarbage.Proof.Seed.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SEED-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.AArch64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cbcEncryptChained
    verified := Proof.Seed.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cbcDecryptChained
    verified := Proof.Seed.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.SeedCbc.AArch64
