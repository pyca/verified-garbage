module

public import VerifiedGarbage.Proof.Idea.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.X86_64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `mul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic CBC of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcEncrypt
    stack := 184
    verified := Proof.Idea.X86_64.cbcEncrypt_framed },
  Spec.Idea.cbcDecryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcDecrypt
    stack := 184
    verified := Proof.Idea.X86_64.cbcDecrypt_framed }]

end VG.Artifacts.IdeaCbc.X86_64
