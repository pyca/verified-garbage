module

public import VerifiedGarbage.Proof.Idea.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit

/-! # IDEA-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.RISCV64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline RV64IM: one block at a time, with ECB's verified block code inlined (each \
  multiplication modulo 2^16 + 1 a `mul` of the residues and a reduction of the product from its \
  halves, without branches), reading the subkeys in place a byte at a time. The mode is the \
  generic one of `Impl/Modes/RISCV64/`, which runs in a frame of 64 bytes on the stack, 16-byte \
  aligned: it keeps its state in `s1`–`s4`, saving our caller's there. The frame is zeroed \
  before returning."

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.Idea.RISCV64.cbcEncryptChained
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Idea.cbcDecryptChainedApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.Idea.RISCV64.cbcDecryptChained
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.IdeaCbc.RISCV64
