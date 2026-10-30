module

public import VerifiedGarbage.Proof.Idea.X86_64.Invert
public import VerifiedGarbage.Proof.Idea.X86_64.Key
public import VerifiedGarbage.Proof.Idea.X86_64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.Lit

/-! # IDEA artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Idea.X86_64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact X86_64.target {
    code := Impl.Idea.X86_64.expandKey
    stack := 0
    verified := Proof.Idea.X86_64.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact X86_64.target {
    code := Impl.Idea.X86_64.invertKey
    stack := 0
    verified := Proof.Idea.X86_64.invertKey_verified },
  Spec.Idea.ecbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 24 .rcx Impl.Idea.X86_64.ecb
    stack := 24
    verified := Proof.Idea.X86_64.ecb_framed }]

end VG.Artifacts.Idea.X86_64
