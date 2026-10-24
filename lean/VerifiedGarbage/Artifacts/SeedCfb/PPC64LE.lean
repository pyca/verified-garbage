module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit

/-! # SEED-CFB128 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.PPC64LE

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
  Spec.Seed.cfbEncryptApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 Impl.Seed.PPC64LE.cfbEncrypt
    stack := 1136
    verified := Proof.Seed.PPC64LE.cfbEnc_framed Proof.Seed.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.Seed.cfbDecryptApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 Impl.Seed.PPC64LE.cfbDecrypt
    stack := 1136
    verified := Proof.Seed.PPC64LE.cfbDec_framed Proof.Seed.PPC64LE.Modes.cfbDecrypt_verified }]

end VG.Artifacts.SeedCfb.PPC64LE
