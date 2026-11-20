module

public import VerifiedGarbage.Proof.Seed.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SEED-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.AArch64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.cbcEncryptChainedCode
    verified := .scrubbed Proof.Seed.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.cbcDecryptChainedCode
    verified := .scrubbed Proof.Seed.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.SeedCbc.AArch64
