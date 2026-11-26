module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Impl.Idea.AArch64.Fn
import VerifiedGarbage.Proof.Idea.AArch64.Invert
import VerifiedGarbage.Proof.Idea.AArch64.Ecb
import VerifiedGarbage.Proof.Idea.AArch64.Key
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.AArch64.Residue
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA on AArch64 -/

namespace VG.Artifacts.Idea.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Idea.expandKeyApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.expandKey
    verified := Proof.Idea.AArch64.Residue.expandKeyCleared_scrubbed },
  Spec.Idea.invertKeyApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.invertKey
    verified := Proof.Idea.AArch64.Residue.invertKeyCleared_scrubbed },
  Spec.Idea.ecbApi.artifact AArch64.target {
    code := Impl.Idea.AArch64.Fn.ecb
    verified := Proof.Idea.AArch64.Residue.ecbCleared_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Idea.AArch64
