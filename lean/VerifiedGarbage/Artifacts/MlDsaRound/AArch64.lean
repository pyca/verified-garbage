module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on AArch64: rounding and hints -/

@[expose] public section

namespace VG.Artifacts.MlDsaRound.AArch64

open VG.Proof.MlDsa.AArch64.Round

def artifacts : List Artifact := [
  Spec.MlDsa.power2RoundApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round
    verified := Proof.MlDsa.AArch64.Optimized.KeygenRound.power2Round_verified },
  Spec.MlDsa.normLtApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Round.normLt
    verified := normLt_verified },
  Spec.MlDsa.useHintApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Round.useHint
    verified := useHint_verified }]

end VG.Artifacts.MlDsaRound.AArch64
