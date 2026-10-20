module

public import VerifiedGarbage.Proof.Idea.X86.Verified
public import VerifiedGarbage.Proof.Idea.X86.Key
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86.Lit

/-! # IDEA artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Idea.X86

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact X86.target {
    notes := ["Baseline IA-32: each 32-bit word of subkeys is a fixed bit permutation of the key's four words, assembled with rotations and masks, without branches."]
    code := Impl.Idea.X86.expandKey
    stack := 0
    verified := Proof.Idea.X86.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact X86.target {
    notes := ["Baseline IA-32: each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mul`, each reduced without branches."]
    code := Impl.StackScratch.X86.withStackScratch 32 2 Impl.Idea.X86.invertKey
    stack := 32
    verified := Proof.Idea.X86.invertKey_framed },
  Spec.Idea.ecbApi.artifact X86.target {
    notes := ["Baseline IA-32, a block at a time in general-purpose registers, with the subkeys copied to a buffer on the stack (zeroed on return): each multiplication modulo 2^16 + 1 is a 32-bit `mul` of the residues and a reduction of the product less one, without branches."]
    code := Impl.StackScratch.X86.withStackScratchWiped 152 3 Proof.Idea.X86.wipedWords Impl.Idea.X86.ecb
    stack := 152
    verified := Proof.Idea.X86.ecb_framed }]

end VG.Artifacts.Idea.X86
