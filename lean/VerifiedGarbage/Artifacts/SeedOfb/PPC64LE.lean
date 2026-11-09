module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit

/-! # SEED-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofb
    stack := 1184
    verified := Proof.Seed.PPC64LE.ofb_framed Proof.Seed.PPC64LE.Modes.ofb_verified },
  Spec.Seed.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofbFinal
    stack := 1184
    verified := Proof.Seed.PPC64LE.FbFinal.ofbFinal_framed }]

end VG.Artifacts.SeedOfb.PPC64LE
