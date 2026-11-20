module

public import VerifiedGarbage.Impl.Idea.AArch64.Fn
public import VerifiedGarbage.Proof.Idea.AArch64.Invert
public import VerifiedGarbage.Proof.Idea.AArch64.Ecb
public import VerifiedGarbage.Proof.Idea.AArch64.Key
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Idea.AArch64.Residue

/-! # IDEA on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Idea.AArch64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.expandKey
    verified := .scrubbed Proof.Idea.AArch64.Residue.expandKeyCleared_scrubbed },
  Spec.Idea.invertKeyApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.invertKey
    verified := .scrubbed Proof.Idea.AArch64.Residue.invertKeyCleared_scrubbed },
  Spec.Idea.ecbApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.ecb
    verified := .scrubbed Proof.Idea.AArch64.Residue.ecbCleared_scrubbed }]

end VG.Artifacts.Idea.AArch64
