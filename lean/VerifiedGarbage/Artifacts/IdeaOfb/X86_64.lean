import VerifiedGarbage.Proof.Idea.X86_64.FbVerified

/-! # IDEA-OFB artifacts on baseline x86-64 -/

namespace VG.Artifacts.IdeaOfb.X86_64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `mul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic OFB of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  { Spec.Idea.ofbApi with
    target := X86_64.target
    doc := Spec.Idea.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.ofb
    contract := Spec.Idea.ofbContract X86_64.abi 184
    stack := 184
    verified := Proof.Idea.X86_64.ofb_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.IdeaOfb.X86_64
