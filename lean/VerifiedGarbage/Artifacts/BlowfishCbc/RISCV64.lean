module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit

/-! # Blowfish-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.RISCV64

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "Baseline RV64I: one block at a time, with ECB's verified block function inlined (each S-box lookup reads all 256 entries of its byte planes under masks, so no address depends on the data or the schedule). The mode is the generic one of `Impl/Modes/RISCV64/`, which runs in a frame of 4224 bytes on the stack, 16-byte aligned: it keeps its state in `s1`–`s4`, saving our caller's there, and the block function reads a copy of the schedule there, made a byte at a time, since the contracts state no alignment for it. The frame is zeroed before returning."

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact RISCV64.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.Blowfish.RISCV64.cbcEncryptChained
    stack := 4224
    verified := Proof.Blowfish.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Blowfish.cbcDecryptChainedApi.artifact RISCV64.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.Blowfish.RISCV64.cbcDecryptChained
    stack := 4224
    verified := Proof.Blowfish.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.BlowfishCbc.RISCV64
