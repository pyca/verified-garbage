module

public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified

/-! # IDEA-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.AArch64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `mul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic OFB of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.Idea.ofbApi with
    target := AArch64.target
    doc := Spec.Idea.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.ofb
    contract := Spec.Idea.ofbContract AArch64.abi 208
    stack := 208
    verified := Proof.Idea.AArch64.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.IdeaOfb.AArch64
