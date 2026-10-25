module

public import VerifiedGarbage.Proof.Seed.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit

/-! # SEED-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86_64

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline x86-64: through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s batch of sixteen blocks \
  (inlined), with SEED's S-boxes computed bitsliced from AES's circuit and no table lookups, grouping the affine layer's parity-specific XOR sums before masking; decryption \
  deciphers sixteen blocks per batch; encryption, whose blocks depend on each other, one, with the other \
  fifteen lanes unused. The schedule is copied into the working space once per call. The mode is the \
  generic CBC of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86_64.target {
    notes := [note, "The IV's address is kept in `xmm15`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 Impl.Seed.X86_64.cbcEncryptChained
    stack := 1512
    verified := Proof.Seed.X86_64.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact X86_64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 Impl.Seed.X86_64.cbcDecryptChained
    stack := 1512
    verified := Proof.Seed.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.X86_64
