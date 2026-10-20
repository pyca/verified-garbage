module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-CFB128 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.AArch64

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline AArch64: through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s batch of sixteen blocks \
  (inlined), with SEED's S-boxes computed bitsliced from AES's circuit and no table lookups; one block per \
  batch, of which the other fifteen lanes are unused. The schedule is copied into the working space once \
  per call. The mode is the generic CFB of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbEncrypt
    stack := 1456
    verified := Proof.Seed.AArch64.cfbEncrypt_framed },
  Spec.Seed.cfbDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbDecrypt
    stack := 1456
    verified := Proof.Seed.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.SeedCfb.AArch64
