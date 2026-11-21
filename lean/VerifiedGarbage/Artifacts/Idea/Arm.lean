module

public import VerifiedGarbage.Proof.Idea.Arm.Scrub
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # IDEA on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Idea.Arm

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.expandKey
    verified := Proof.Idea.Arm.Fn.expandKey },
  Spec.Idea.invertKeyApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.invertKey
    verified := Proof.Idea.Arm.Fn.invertKey },
  Spec.Idea.ecbApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.ecb
    verified := Proof.Idea.Arm.Fn.ecb }]

end VG.Artifacts.Idea.Arm
