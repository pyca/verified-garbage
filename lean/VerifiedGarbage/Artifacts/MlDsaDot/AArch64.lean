module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
public import VerifiedGarbage.TCB.AArch64.Target
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaDot.AArch64

def dotArtifact (count : Nat) (hc : count=4 ∨ count=5 ∨ count=7) : Artifact :=
  (Spec.MlDsa.dotInverseApi count).artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode count
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.dot_verified hc }

def artifacts : List Artifact := [dotArtifact 4 (by simp),dotArtifact 5 (by simp),dotArtifact 7 (by simp)]

end VG.Artifacts.MlDsaDot.AArch64
