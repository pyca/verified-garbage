module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Power2Round
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.HighLow
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.NormLt
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.MakeHint
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.UseHint
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on PPC64LE: rounding and hints -/

@[expose] public section

namespace VG.Artifacts.MlDsaRound.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.power2RoundApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Round.power2Round
    verified := Proof.MlDsa.PPC64LE.Round.Power2Round.verified },
  Spec.MlDsa.highBitsApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Round.highBits
    verified := Proof.MlDsa.PPC64LE.Round.HighLow.high_verified },
  Spec.MlDsa.lowBitsApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Round.lowBits
    verified := Proof.MlDsa.PPC64LE.Round.HighLow.low_verified },
  Spec.MlDsa.normLtApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Round.normLt
    verified := Proof.MlDsa.PPC64LE.Round.NormLt.verified },
  Spec.MlDsa.makeHintApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Round.makeHint
    verified := Proof.MlDsa.PPC64LE.Round.MakeHint.verified },
  Spec.MlDsa.useHintApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Round.useHint
    verified := Proof.MlDsa.PPC64LE.Round.UseHint.verified }]

end VG.Artifacts.MlDsaRound.PPC64LE
