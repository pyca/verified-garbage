module

public import VerifiedGarbage.Proof.Idea.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit

/-! # IDEA-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.X86_64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `imul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic CBC of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact X86_64.target {
    notes := [note, "The IV's address is kept in `xmm15`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcEncryptChained
    stack := 184
    verified := Proof.Idea.X86_64.cbcEncryptChained_framed },
  Spec.Idea.cbcDecryptChainedApi.artifact X86_64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcDecryptChained
    stack := 184
    verified := Proof.Idea.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.IdeaCbc.X86_64
