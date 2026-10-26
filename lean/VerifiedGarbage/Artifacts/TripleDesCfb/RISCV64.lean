module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CFB64 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.RISCV64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline RV64I: one block at a time, with ECB's verified block function inlined (Boolean S-box \
  circuits and no table lookups). The mode is the generic one of `Impl/Modes/RISCV64/`, which runs \
  in a frame of 640 bytes on the stack, 16-byte aligned: it keeps its state in `s1`–`s4`, saving \
  our caller's there, and the block function reads a copy of the schedule there, made a byte at a \
  time, since the contracts state no alignment for it. The frame is zeroed before returning."

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.TripleDes.RISCV64.cfbEncrypt
    stack := 640
    verified := Proof.TripleDes.RISCV64.Modes.cfbEncrypt_verified },
  Spec.TripleDes.cfbDecryptApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.TripleDes.RISCV64.cfbDecrypt
    stack := 640
    verified := Proof.TripleDes.RISCV64.Modes.cfbDecrypt_verified }]

end VG.Artifacts.TripleDesCfb.RISCV64
