module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
import Std.Data.DTreeMap.Internal.Operations
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.DotInverse
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MlDsa.FusedInverse
public import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Artifacts.MlDsaDot.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.dotInverseApi 4).artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode 4
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.dot_verified (.inl rfl) },
  (Spec.MlDsa.dotInverseApi 5).artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode 5
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.dot_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.dotInverseApi 7).artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode 7
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.dot_verified (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsaDot.AArch64
