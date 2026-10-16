module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackVerified
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaUseHintPack.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.useHintPackApi 261888).artifact VG.AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
    verified := Proof.MlDsa.AArch64.Optimized.UseHintPack.pack_verified (by decide)
    spSafe := Code.all_of_forall (fun _=>rfl) _ },
  (Spec.MlDsa.useHintPackApi 95232).artifact VG.AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
    verified := Proof.MlDsa.AArch64.Optimized.UseHintPack.pack_verified (by decide)
    spSafe := Code.all_of_forall (fun _=>rfl) _ }]

end VG.Artifacts.MlDsaUseHintPack.AArch64
