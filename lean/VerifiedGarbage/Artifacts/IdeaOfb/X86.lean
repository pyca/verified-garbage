module

public import VerifiedGarbage.Proof.Idea.X86.FbVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Idea.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit

/-! # IDEA-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.X86

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.ofb
    stack := 208
    verified := Proof.Idea.X86.Fb.ofb_framed },
  Spec.Idea.ofbFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.ofbFinal
    stack := 208
    verified := Proof.Idea.X86.FbFinal.ofbFinal_framed }]

end VG.Artifacts.IdeaOfb.X86
