module

public import VerifiedGarbage.Proof.Idea.AArch64.Invert
public import VerifiedGarbage.Proof.Idea.AArch64.Ecb
public import VerifiedGarbage.Proof.Idea.AArch64.Key
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # IDEA artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Idea.AArch64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64: each quadword of subkeys is a fixed bit permutation of the key's two quadwords, assembled with rotations and masks, without branches."]
    code := Impl.Idea.AArch64.expandKey
    stack := 0
    verified := Proof.Idea.AArch64.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64: each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mul`, each reduced without branches."]
    code := Impl.Idea.AArch64.invertKey
    stack := 0
    verified := Proof.Idea.AArch64.invertKey_verified },
  Spec.Idea.ecbApi.artifact AArch64.target {
    notes := ["Baseline AArch64, a block at a time in general-purpose registers: each multiplication modulo 2^16 + 1 is a `mul` and a reduction without branches."]
    code := Impl.Idea.AArch64.ecb
    stack := 0
    verified := Proof.Idea.AArch64.ecb_verified }]

end VG.Artifacts.Idea.AArch64
