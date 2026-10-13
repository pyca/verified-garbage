module

public import VerifiedGarbage.Proof.Idea.X86.FbVerified

/-! # IDEA-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.X86

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, with branch-free ⊙ (`mul`, whose timing does not depend on its \
  operands), the subkeys copied to the stack once per call. The mode is the generic OFB of `Impl/Modes/X86/`, \
  over IDEA's ECB block."

def artifacts : List Artifact := [
  { Spec.Idea.ofbApi with
    target := X86.target
    doc := Spec.Idea.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.ofb
    contract := Spec.Idea.ofbContract X86.abi 208
    stack := 208
    verified := Proof.Idea.X86.Fb.ofb_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.IdeaOfb.X86
