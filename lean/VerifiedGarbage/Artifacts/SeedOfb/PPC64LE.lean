module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit

/-! # SEED-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.ofb
    verified := .scrubbed Proof.Seed.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Seed.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Seed.PPC64LE.Fn.ofbFinal
    verified := .scrubbed Proof.Seed.PPC64LE.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.SeedOfb.PPC64LE
