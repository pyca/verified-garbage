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
  "Baseline PPC64LE: one block at a time, each a call of `vg_seed_encrypt_blocks` or \
  `vg_seed_decrypt_blocks` on a batch of one, with SEED's S-boxes computed bitsliced from AES's \
  circuit and no table lookups, the other fifteen lanes unused, reading the round keys in place. The \
  mode is the generic one of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31` and saves \
  the return address in the working space; the blocks function saves and restores every callee-saved \
  register, and leaves the working space's address in `r8`, from which the core takes the scratch \
  buffer's address back. The working space (1152 bytes, the blocks function's 1088 among them) is on \
  the stack, zeroed before returning."

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact PPC64LE.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cbcEncryptChained
    stack := 1184
    verified := Proof.Seed.PPC64LE.cbcEnc_framed Proof.Seed.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.Seed.cbcDecryptChainedApi.artifact PPC64LE.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cbcDecryptChained
    stack := 1184
    verified := Proof.Seed.PPC64LE.cbcDec_framed Proof.Seed.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.SeedCbc.PPC64LE
