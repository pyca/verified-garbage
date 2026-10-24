module
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Avx2Lit

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on x86-64: the sampling primitives -/

@[expose] public section

namespace VG.Artifacts.MlDsaSample.X86_64

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.rejNTTApi.artifact X86_64.target {
    notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them."]
    code := Impl.MlDsa.X86_64.Sample.rejNTT
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.rejNTT_verified },
  Spec.MlDsa.rejNTT4Api.artifact X86_64.target {
    notes := ["It calls `vg_mldsa_rej_ntt_poly` on each seed, and saves \
      its caller's callee-saved registers in `scratch`."]
    code := Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4
    stack := 24
    verified := Proof.MlDsa.X86_64.Rej4.rejNTT4_verified },
  Spec.MlDsa.rejNTT4Api.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["It runs the four instances of SHAKE128 at once, in the four \
      64-bit elements of AVX2 registers. It first samples from five blocks (840 bytes) per seed, and \
      squeezes a sixth block only if any polynomial is incomplete. Its coefficients and six-block \
      failure bound match `vg_mldsa_rej_ntt_poly`. It saves callee-saved registers in `scratch`."]
    code := Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2
    stack := 24
    verified := Proof.MlDsa.X86_64.Rej4.Segment.rejNTT4Avx2_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.rejBoundedApi.artifact X86_64.target {
    notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of an accepted half-byte is computed \
      without a branch or a table, so only whether each half-byte is accepted affects timing."]
    code := Impl.MlDsa.X86_64.Sample.rejBounded
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.rejBounded_verified },
  Spec.MlDsa.expandMaskApi.artifact X86_64.target {
    notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks four coefficients at a time."]
    code := Impl.MlDsa.X86_64.Sample.expandMask
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.expandMask_verified },
  Spec.MlDsa.expandMask4Api.artifact X86_64.target {
    notes := ["It calls `vg_mldsa_expand_mask_poly` on each seed, and \
      saves its caller's callee-saved registers in `scratch`."]
    code := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4
    stack := 24
    verified := Proof.MlDsa.X86_64.Mask4.expandMask4_verified },
  Spec.MlDsa.expandMask4Api.artifact X86_64.target {
    suffix := "_avx2"
    notes := ["It runs the four instances of SHAKE256 at once, in the \
      four 64-bit elements of AVX2 registers (as `vg_mldsa_rej_ntt_poly4_avx2` does with SHAKE128), \
      squeezing five blocks of each, and unpacks the 576 or 640 bytes of each seed's output as \
      `vg_mldsa_expand_mask_poly` does. It saves its caller's callee-saved registers in `scratch`."]
    code := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4Avx2
    stack := 24
    verified := Proof.MlDsa.X86_64.Mask4.expandMask4Avx2_verified
    features := ["avx", "avx2"] },
  Spec.MlDsa.sampleInBallApi.artifact X86_64.target {
    notes := ["It squeezes 272 bytes of SHAKE256 output (2 blocks) and \
      runs the loop of `SampleInBall` over the 264 after the sign bits."]
    code := Impl.MlDsa.X86_64.Sample.sampleInBall
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.sampleInBall_verified }]

end VG.Artifacts.MlDsaSample.X86_64
