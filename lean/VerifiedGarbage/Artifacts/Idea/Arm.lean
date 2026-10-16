module

public import VerifiedGarbage.Proof.Idea.Arm.Verified
public import VerifiedGarbage.Proof.Idea.Arm.Key
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Idea.Arm

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact Arm.target {
    notes := ["Baseline ARMv7: each 32-bit word of subkeys is a fixed bit permutation of the key's four words, assembled with rotations and masks, without branches."]
    code := Impl.Idea.Arm.expandKey
    stack := 0
    verified := Proof.Idea.Arm.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact Arm.target {
    notes := ["Baseline ARMv7: each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mul`, each reduced without branches."]
    code := Impl.StackScratch.Arm.withRegScratch 24 .r2 Impl.Idea.Arm.invertKey
    stack := 24
    verified := Proof.Idea.Arm.invertKey_framed },
  Spec.Idea.ecbApi.artifact Arm.target {
    notes := ["Baseline ARMv7, a block at a time in general-purpose registers: each multiplication modulo 2^16 + 1 is a 32-bit `mul` of the residues and a reduction of the product less one, without branches."]
    code := Impl.StackScratch.Arm.withRegScratch 32 .r3 Impl.Idea.Arm.ecb
    stack := 32
    verified := Proof.Idea.Arm.ecb_framed }]

end VG.Artifacts.Idea.Arm
