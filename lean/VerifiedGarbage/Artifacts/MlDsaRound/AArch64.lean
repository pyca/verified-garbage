module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Bits
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.MakeHint
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on AArch64: rounding and hints -/

@[expose] public section

namespace VG.Artifacts.MlDsaRound.AArch64

open VG.Proof.MlDsa.AArch64.Round

def artifacts : List Artifact := [
  Spec.MlDsa.power2RoundApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Round.power2Round
    verified := power2Round_verified },
  Spec.MlDsa.highBitsApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Round.highBits
    verified := highBits_verified },
  Spec.MlDsa.lowBitsApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Round.lowBits
    verified := lowBits_verified },
  Spec.MlDsa.normLtApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Round.normLt
    verified := normLt_verified },
  Spec.MlDsa.makeHintApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Round.makeHint
    verified := makeHint_verified },
  Spec.MlDsa.useHintApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Round.useHint
    verified := useHint_verified }]

end VG.Artifacts.MlDsaRound.AArch64
