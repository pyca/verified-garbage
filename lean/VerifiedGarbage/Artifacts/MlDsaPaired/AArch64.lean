module

public import VerifiedGarbage.Spec.MlDsa.PairedApi
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCorrect
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaPaired.AArch64

def artifacts : List Artifact := [
  Spec.MlDsa.pairedZApi.artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts
    code := Impl.MlDsa.AArch64.Optimized.Paired.selected .z
    verified := Proof.MlDsa.AArch64.Optimized.Paired.pairedZ_verified },
  Spec.MlDsa.pairedLowApi.artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts
    code := Impl.MlDsa.AArch64.Optimized.Paired.selected .r0
    verified := Proof.MlDsa.AArch64.Optimized.Paired.pairedLow_verified },
  Spec.MlDsa.pairedHintApi.artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Paired.pairedConsts
    code := Impl.MlDsa.AArch64.Optimized.Paired.selected .h
    verified := Proof.MlDsa.AArch64.Optimized.Paired.pairedHint_verified }]

end VG.Artifacts.MlDsaPaired.AArch64
