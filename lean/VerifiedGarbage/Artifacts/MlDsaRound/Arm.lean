module

public import VerifiedGarbage.Proof.MlDsa.Arm.Round.Power2Round
public import VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt
public import VerifiedGarbage.Proof.MlDsa.Arm.Round.MakeHint
public import VerifiedGarbage.Proof.MlDsa.Arm.Round.UseHint
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on 32-bit ARM: rounding and hints -/

@[expose] public section

namespace VG.Artifacts.MlDsaRound.Arm

open VG.Proof.MlDsa.Arm.Round

def artifacts : List Artifact := [
  Spec.MlDsa.power2RoundApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Round.power2Round
    stack := 4
    verified := P2R.verified },
  Spec.MlDsa.highBitsApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Round.highBits
    verified := Bits.high_verified },
  Spec.MlDsa.lowBitsApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Round.lowBits
    verified := Bits.low_verified },
  Spec.MlDsa.normLtApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Round.normLt
    stack := 4
    verified := NormLt.verified },
  Spec.MlDsa.makeHintApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Round.makeHint
    stack := 12
    verified := MakeHint.verified },
  Spec.MlDsa.useHintApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Round.useHint
    stack := 12
    verified := UseHint.verified }]

end VG.Artifacts.MlDsaRound.Arm
