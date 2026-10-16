module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YUse
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on x86-64: rounding and hints -/

@[expose] public section

namespace VG.Artifacts.MlDsaRound.X86_64

open VG.Proof.MlDsa.X86_64.Round

def artifacts : List Artifact := [
  Spec.MlDsa.power2RoundApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.power2Round
    verified := power2Round_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.highBitsApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.highBits
    verified := highBits_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.lowBitsApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.lowBits
    verified := lowBits_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.highBitsApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 \
      registers, multiplying by shifts and additions; it needs AVX and AVX2."]
    code := Impl.MlDsa.X86_64.Round.highBitsAvx2
    verified := highBitsY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  Spec.MlDsa.lowBitsApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 \
      registers, multiplying by shifts and additions; it needs AVX and AVX2."]
    code := Impl.MlDsa.X86_64.Round.lowBitsAvx2
    verified := lowBitsY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  Spec.MlDsa.normLtApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.normLt
    verified := normLt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.makeHintApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.makeHint
    verified := makeHint_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.normLtApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function compares eight coefficients at a time in AVX2 \
      registers; it needs AVX and AVX2."]
    code := Impl.MlDsa.X86_64.Round.normLtAvx2
    verified := normLtY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  Spec.MlDsa.makeHintApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes eight hints at a time in AVX2 \
      registers, multiplying by shifts and additions; it needs AVX and AVX2."]
    code := Impl.MlDsa.X86_64.Round.makeHintAvx2
    verified := makeHintY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  Spec.MlDsa.useHintApi.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.Round.useHint
    verified := useHint_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.useHintApi.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["The function computes on eight coefficients at a time in AVX2 \
      registers, multiplying by shifts and additions; it needs AVX and AVX2."]
    code := Impl.MlDsa.X86_64.Round.useHintAvx2
    verified := useHintY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlDsaRound.X86_64
