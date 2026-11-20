module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public import VerifiedGarbage.Proof.Seed.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
import VerifiedGarbage.Proof.Seed.AArch64.FbFinalLit

/-! # SEED-OFB on AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.AArch64

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.ofbCode
    verified := .scrubbed Proof.Seed.AArch64.ModesResidue.ofbCode_scrubbed },
  Spec.Seed.ofbFinalApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.ofbFinalCode
    verified := .scrubbed Proof.Seed.AArch64.ModesResidue.ofbFinalCode_scrubbed }]

end VG.Artifacts.SeedOfb.AArch64
