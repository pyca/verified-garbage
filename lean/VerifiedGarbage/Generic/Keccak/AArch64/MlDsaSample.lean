module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatchTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on AArch64: the sampling primitives -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaSample

open VG

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.rejNTT4Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := ["Four SHAKE128 streams in two pairs of NEON lanes, \
      using ARM SHA3 instructions when available. The SHA3 path keeps five blocks resident and \
      squeezes a sixth block only if needed; the portable path always squeezes six."]
    code := Impl.MlDsa.AArch64.Optimized.ResidentRej.selected v.callee.pairedSha3
    verified := Proof.MlDsa.AArch64.Optimized.ResidentRej.selected_verified v.callee.pairedSha3 },
  Spec.MlDsa.rejNTTApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them."]
    code := Impl.MlDsa.AArch64.Sample.rejNTTWith v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.rejNTT_verifiedWith v },
  Spec.MlDsa.rejBoundedApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of a half-byte is computed and stored \
      without a branch or a table, and counted only if the half-byte is accepted, so only whether each \
      half-byte is accepted affects timing."]
    code := Impl.MlDsa.AArch64.Sample.rejBoundedWith v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.rejBounded_verifiedWith v },
  Spec.MlDsa.expandMaskApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks four coefficients at a time."]
    code := Impl.MlDsa.AArch64.Sample.expandMaskWith v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.expandMask_verifiedWith v },
  Spec.MlDsa.sampleInBallApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := ["SHA3 sampling stops once all coefficients are assigned and squeezes the second block \
      only when needed. Both paths retain the same 272-byte limit and exact failure result."]
    code := Impl.MlDsa.AArch64.Optimized.Ball.selected v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.Optimized.Ball.selected_verified v }]

end VG.Generic.Keccak.AArch64.MlDsaSample
