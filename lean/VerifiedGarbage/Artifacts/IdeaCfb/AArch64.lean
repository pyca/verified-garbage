module

public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CFB64 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.AArch64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `mul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic CFB of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbEncrypt
    stack := 208
    verified := Proof.Idea.AArch64.cfbEncrypt_framed },
  Spec.Idea.cfbDecryptApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbDecrypt
    stack := 208
    verified := Proof.Idea.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.IdeaCfb.AArch64
