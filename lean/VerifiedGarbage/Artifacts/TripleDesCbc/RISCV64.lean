module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.RISCV64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline RV64I: one block at a time, with ECB's verified block function inlined (Boolean S-box \
  circuits and no table lookups). The mode is the generic one of `Impl/Modes/RISCV64/`, which runs \
  in a frame of 640 bytes on the stack, 16-byte aligned: it keeps its state in `s1`–`s4`, saving \
  our caller's there, and the block function reads a copy of the schedule there, made a byte at a \
  time, since the contracts state no alignment for it. The frame is zeroed before returning."

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.TripleDes.RISCV64.cbcEncryptChained
    stack := 640
    verified := Proof.TripleDes.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.TripleDes.cbcDecryptChainedApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.TripleDes.RISCV64.cbcDecryptChained
    stack := 640
    verified := Proof.TripleDes.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.TripleDesCbc.RISCV64
