module

public import VerifiedGarbage.Proof.Seed.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.AArch64

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline AArch64: through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s batch of sixteen blocks \
  (inlined), with SEED's S-boxes computed bitsliced from AES's circuit and no table lookups; decryption \
  deciphers sixteen blocks per batch; encryption, whose blocks depend on each other, one, with the other \
  fifteen lanes unused. The schedule is copied into the working space once per call. The mode is the \
  generic CBC of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact AArch64.target {
    notes := [note, "The IV's address is kept in `x25`, which the core keeps in `v31`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcEncryptChained
    stack := 1456
    verified := Proof.Seed.AArch64.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact AArch64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcDecryptChained
    stack := 1456
    verified := Proof.Seed.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.AArch64
