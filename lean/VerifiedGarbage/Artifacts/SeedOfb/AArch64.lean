module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.AArch64

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline AArch64: through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s batch of sixteen blocks \
  (inlined), with SEED's S-boxes computed bitsliced from AES's circuit and no table lookups; one block per \
  batch, of which the other fifteen lanes are unused. The schedule is copied into the working space once \
  per call. The mode is the generic OFB of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.ofb
    stack := 1456
    verified := Proof.Seed.AArch64.ofb_framed }]

end VG.Artifacts.SeedOfb.AArch64
