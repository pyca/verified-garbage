module

public import VerifiedGarbage.Proof.Seed.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit

/-! # SEED-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.RISCV64

/-- How the functions compute SEED, and the mode. -/
def note : String :=
  "Baseline RV64IM: one block at a time, through `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`'s \
  batch of sixteen (inlined, with ECB's setup), with SEED's S-boxes computed bitsliced from AES's \
  circuit and no table lookups, the other fifteen lanes unused, reading the round keys in place. \
  The mode is the generic one of `Impl/Modes/RISCV64/`, which keeps its state in `s1`–`s4`; the \
  rounds use every callee-saved register, so around each block our caller's `s0`–`s11` are saved \
  in ECB's working space, the modes' `s1`–`s3` wait in `a1`, `a2` and `ra`, and `ra` in the \
  frame. The frame (1104 bytes, ECB's working space among them) is on the stack, 16-byte aligned, \
  zeroed before returning."

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.Seed.RISCV64.cbcEncryptChained
    stack := 1104
    verified := Proof.Seed.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Seed.cbcDecryptChainedApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.Seed.RISCV64.cbcDecryptChained
    stack := 1104
    verified := Proof.Seed.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.SeedCbc.RISCV64
