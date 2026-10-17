module

public import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.AArch64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `mul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic CBC of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact AArch64.target {
    notes := [note, "The IV's address is kept in `x25`, which the core keeps, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcEncryptChained
    stack := 208
    verified := Proof.Idea.AArch64.cbcEncryptChained_framed },
  Spec.Idea.cbcDecryptChainedApi.artifact AArch64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcDecryptChained
    stack := 208
    verified := Proof.Idea.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.IdeaCbc.AArch64
