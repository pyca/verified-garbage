module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CFB8 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.RISCV64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline RV64I: one block at a time, with ECB's verified block function inlined (the eight S-boxes \
  looked up at once in the 64 lanes of a word, from words of constants in the frame, with no \
  table lookups at secret addresses). The mode is the generic one of `Impl/Modes/RISCV64/`, which runs \
  in a frame of 944 bytes on the stack, 16-byte aligned: it keeps its state in `s1`–`s4`, saving \
  our caller's there, and the block function reads a copy of the schedule there, made a byte at a \
  time, since the contracts state no alignment for it. The frame is zeroed before returning."

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.TripleDes.RISCV64.cfb8Encrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfb8Encrypt_verified },
  Spec.TripleDes.cfb8DecryptApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.TripleDes.RISCV64.cfb8Decrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfb8Decrypt_verified }]

end VG.Artifacts.TripleDesCfb8.RISCV64
