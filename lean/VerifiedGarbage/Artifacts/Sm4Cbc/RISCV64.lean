module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.RISCV64

/-- How the functions compute SM4, and the mode. -/
def note : String :=
  "Baseline RV64IM: one block at a time, bitsliced in general-purpose registers through the AES \
  S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in \
  `vg_sm4_ecb_encrypt`'s batch of sixteen (inlined) of which the other fifteen are unused: the \
  table of bitsliced round keys is built once per call, as `vg_sm4_prepare_keys` builds it, in \
  ECB's working space. The mode is the generic one of `Impl/Modes/RISCV64/`, which keeps its \
  state in `s1`–`s4`; the rounds use every callee-saved register, so around each block our \
  caller's `s0`–`s11` are saved in ECB's working space, the modes' `s1`–`s3` wait in `a1`, `a2` \
  and `a4`, and the schedule's address in the frame. The frame (3232 bytes, ECB's working space \
  among them) is on the stack, 16-byte aligned, zeroed before returning."

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact RISCV64.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.Sm4.RISCV64.cbcEncryptChained
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Sm4.cbcDecryptChainedApi.artifact RISCV64.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.Sm4.RISCV64.cbcDecryptChained
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.Sm4Cbc.RISCV64
