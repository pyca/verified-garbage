module

public import VerifiedGarbage.Proof.Seed.AArch64.CbcVerified
import Mathlib.Tactic.SplitIfs

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
  { Spec.Seed.cbcEncryptApi with
    target := AArch64.target
    doc := Spec.Seed.cbcEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcEncrypt
    contract := Spec.Seed.cbcEncryptContract AArch64.abi 1456
    stack := 1456
    verified := Proof.Seed.AArch64.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Seed.cbcDecryptApi with
    target := AArch64.target
    doc := Spec.Seed.cbcDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcDecrypt
    contract := Spec.Seed.cbcDecryptContract AArch64.abi 1456
    stack := 1456
    verified := Proof.Seed.AArch64.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.SeedCbc.AArch64
