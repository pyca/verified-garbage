module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified

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
  { Spec.Seed.ofbApi with
    target := AArch64.target
    doc := Spec.Seed.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.ofb
    contract := Spec.Seed.ofbContract AArch64.abi 1456
    stack := 1456
    verified := Proof.Seed.AArch64.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.SeedOfb.AArch64
