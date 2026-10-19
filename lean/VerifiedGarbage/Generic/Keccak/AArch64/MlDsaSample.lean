module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

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
  Spec.MlDsa.sampleInBallApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := ["SHA3 sampling stops once all coefficients are assigned and squeezes the second block \
      only when needed. Both paths retain the same 272-byte limit and exact failure result."]
    code := Impl.MlDsa.AArch64.Optimized.Ball.selected v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.Optimized.Ball.selected_verified v }] ++
  -- Only the SHA-3 extension's signing calls `ExpandMask` one polynomial at a
  -- time (`vg_mldsa_expand_mask_poly_sha3`).
  if v.callee.pairedSha3 then [
    Spec.MlDsa.expandMaskApi.artifact AArch64.target {
      suffix := v.callee.suffix
      features := v.features
      notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
        which hold the 576 or 640 bytes it unpacks) and unpacks four coefficients at a time."]
      code := Impl.MlDsa.AArch64.Sample.expandMaskWith v.callee
      stack := 16
      verified := Proof.MlDsa.AArch64.Sample.expandMask_verifiedWith v }] else []

end VG.Generic.Keccak.AArch64.MlDsaSample
