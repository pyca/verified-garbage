module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackVerified
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.UseHintPack
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MlDsa.UseHintPack
public import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Artifacts.MlDsaUseHintPack.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.useHintPackApi 261888).artifact VG.AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
    verified := Proof.MlDsa.AArch64.Optimized.UseHintPack.pack_verified (.inl rfl) },
  (Spec.MlDsa.useHintPackApi 95232).artifact VG.AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
    verified := Proof.MlDsa.AArch64.Optimized.UseHintPack.pack_verified (.inr rfl) }]

end VG.Artifacts.MlDsaUseHintPack.AArch64
