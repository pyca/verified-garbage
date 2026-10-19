module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MlDsa.MontDot
public import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Artifacts.MlDsaMontDot.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.montDotApi 4).artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.MontDot.dot 4
    verified := Proof.MlDsa.AArch64.Optimized.MontDot.verified (.inl rfl) },
  (Spec.MlDsa.montDotApi 5).artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.MontDot.dot 5
    verified := Proof.MlDsa.AArch64.Optimized.MontDot.verified (.inr (.inl rfl)) },
  (Spec.MlDsa.montDotApi 7).artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.MontDot.dot 7
    verified := Proof.MlDsa.AArch64.Optimized.MontDot.verified (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsaMontDot.AArch64
