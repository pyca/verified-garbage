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
  Spec.Idea.cbcEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcEncrypt
    stack := 208
    verified := Proof.Idea.AArch64.cbcEncrypt_framed },
  Spec.Idea.cbcDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcDecrypt
    stack := 208
    verified := Proof.Idea.AArch64.cbcDecrypt_framed }]

end VG.Artifacts.IdeaCbc.AArch64
