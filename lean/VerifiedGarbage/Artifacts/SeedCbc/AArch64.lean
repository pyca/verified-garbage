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
  Spec.Seed.cbcEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcEncrypt
    stack := 1456
    verified := Proof.Seed.AArch64.cbcEncrypt_framed },
  Spec.Seed.cbcDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcDecrypt
    stack := 1456
    verified := Proof.Seed.AArch64.cbcDecrypt_framed }]

end VG.Artifacts.SeedCbc.AArch64
