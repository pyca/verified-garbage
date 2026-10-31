module
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit

public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Power2Round
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YUse
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YNorm
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on x86-64: rounding and hints -/

@[expose] public section

namespace VG.Artifacts.MlDsaRound.X86_64

open VG.Proof.MlDsa.X86_64.Round

def artifacts : List Artifact := [
  Spec.MlDsa.power2RoundApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.power2Round
    verified := power2Round_verified },
  Spec.MlDsa.highBitsApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.highBits
    verified := highBits_verified },
  Spec.MlDsa.lowBitsApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.lowBits
    verified := lowBits_verified },
  Spec.MlDsa.highBitsApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlDsa.X86_64.Round.highBitsAvx2
    verified := highBitsY_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.lowBitsApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlDsa.X86_64.Round.lowBitsAvx2
    verified := lowBitsY_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.normLtApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.normLt
    verified := normLt_verified },
  Spec.MlDsa.makeHintApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.makeHint
    verified := makeHint_verified },
  Spec.MlDsa.normLtApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlDsa.X86_64.Round.normLtAvx2
    verified := normLtY_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.makeHintApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlDsa.X86_64.Round.makeHintAvx2
    verified := makeHintY_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.useHintApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.useHint
    verified := useHint_verified },
  Spec.MlDsa.useHintApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.MlDsa.X86_64.Round.useHintAvx2
    verified := useHintY_verified
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlDsaRound.X86_64
