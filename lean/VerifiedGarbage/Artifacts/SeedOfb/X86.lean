module

public import VerifiedGarbage.Proof.Seed.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.FbLit

/-! # SEED-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86

/-- How the function computes SEED, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time (each output block is the encryption of the one before), encrypted bitsliced in general-purpose registers \
  through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups, in a batch of \
  eight of which the other seven are unused; the table of round keys is built from the schedule once per call. \
  The mode is the generic OFB of `Impl/Modes/X86/`, over SEED's ECB core."

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 888 4 216 Impl.Seed.X86.ofb
    stack := 888
    verified := Proof.Seed.X86.Fb.ofb_framed }]

end VG.Artifacts.SeedOfb.X86
