module

public import VerifiedGarbage.Proof.Idea.X86.CbcVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86.ModesLit

/-! # IDEA-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.X86

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, with branch-free ⊙ (`mul`, whose timing does not depend on its \
  operands), the subkeys copied to the stack once per call. The mode is the generic CBC of `Impl/Modes/X86/`, \
  over IDEA's ECB block."

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact X86.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cbcEncryptChained
    stack := 208
    verified := Proof.Idea.X86.Cbc.cbcEncryptChained_framed },
  Spec.Idea.cbcDecryptChainedApi.artifact X86.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cbcDecryptChained
    stack := 208
    verified := Proof.Idea.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.IdeaCbc.X86
