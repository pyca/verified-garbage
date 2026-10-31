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
    code := Impl.Idea.AArch64.expandKey
    stack := 0
    verified := Proof.Idea.AArch64.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.invertKey
    stack := 0
    verified := Proof.Idea.AArch64.invertKey_verified },
  Spec.Idea.ecbApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.ecb
    stack := 0
    verified := Proof.Idea.AArch64.ecb_verified }]

end VG.Artifacts.Idea.AArch64
