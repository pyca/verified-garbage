module

public import VerifiedGarbage.Proof.Seed.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit

/-! # SEED-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86_64

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline x86-64: through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s batch of sixteen blocks \
  (inlined), with SEED's S-boxes computed bitsliced from AES's circuit and no table lookups; one block per \
  batch, of which the other fifteen lanes are unused. The schedule is copied into the working space once \
  per call. The mode is the generic OFB of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 Impl.Seed.X86_64.ofb
    stack := 1512
    verified := Proof.Seed.X86_64.ofb_framed }]

end VG.Artifacts.SeedOfb.X86_64
