module

public import VerifiedGarbage.Proof.Idea.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit

/-! # IDEA-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.RISCV64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline RV64IM: one block at a time, with ECB's verified block code inlined (each \
  multiplication modulo 2^16 + 1 a `mul` of the residues and a reduction of the product from its \
  halves, without branches), reading the subkeys in place a byte at a time. The mode is the \
  generic one of `Impl/Modes/RISCV64/`, which runs in a frame of 64 bytes on the stack, 16-byte \
  aligned: it keeps its state in `s1`–`s4`, saving our caller's there. The frame is zeroed \
  before returning."

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact RISCV64.target {
    notes := [note]
    code := Impl.Idea.RISCV64.ofb
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.ofb_verified }]

end VG.Artifacts.IdeaOfb.RISCV64
