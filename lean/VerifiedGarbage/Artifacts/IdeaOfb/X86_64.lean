module

public import VerifiedGarbage.Proof.Idea.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit

/-! # IDEA-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.X86_64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `imul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic OFB of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.ofb
    stack := 184
    verified := Proof.Idea.X86_64.ofb_framed }]

end VG.Artifacts.IdeaOfb.X86_64
