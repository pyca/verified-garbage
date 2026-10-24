module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit

/-! # SEED-CBC artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.PPC64LE

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s \
  batch of sixteen (inlined), with SEED's S-boxes computed bitsliced from AES's circuit and no table \
  lookups, the other fifteen lanes unused, reading the round keys in place. The mode is the generic \
  one of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31`; the rounds use every \
  callee-saved register, so around each block the caller's `r14`–`r28` are saved in the working \
  space and the modes' state waits in `r4`–`r6`. The working space (1104 bytes) is on the stack, \
  zeroed before returning."

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact PPC64LE.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 Impl.Seed.PPC64LE.cbcEncryptChained
    stack := 1136
    verified := Proof.Seed.PPC64LE.cbcEnc_framed Proof.Seed.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.Seed.cbcDecryptChainedApi.artifact PPC64LE.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 Impl.Seed.PPC64LE.cbcDecryptChained
    stack := 1136
    verified := Proof.Seed.PPC64LE.cbcDec_framed Proof.Seed.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.SeedCbc.PPC64LE
