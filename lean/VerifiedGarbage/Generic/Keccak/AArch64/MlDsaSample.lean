import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball

/-! # ML-DSA (FIPS 204) on AArch64: the sampling primitives -/

namespace VG.Generic.Keccak.AArch64.MlDsaSample

open VG

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlDsa.rejNTT4Api with
    name := Spec.MlDsa.rejNTT4Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.rejNTT4Api.doc (notes := ["Four SHAKE128 streams in two pairs of NEON lanes, \
      using ARM SHA3 instructions when available. The SHA3 path keeps five blocks resident and \
      squeezes a sixth block only if needed; the portable path always squeezes six."])
    code := Impl.MlDsa.AArch64.Optimized.ResidentRej.selected v.callee.pairedSha3
    contract := Spec.MlDsa.rejNTT4Contract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.ResidentRej.selected_verified v.callee.pairedSha3
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.rejNTTApi with
    name := Spec.MlDsa.rejNTTApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.rejNTTApi.doc (notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them."])
    code := Impl.MlDsa.AArch64.Sample.rejNTTWith v.callee
    contract := Spec.MlDsa.rejNTTContract AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.rejNTT_verifiedWith v
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.rejBoundedApi with
    name := Spec.MlDsa.rejBoundedApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.rejBoundedApi.doc (notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of a half-byte is computed and stored \
      without a branch or a table, and counted only if the half-byte is accepted, so only whether each \
      half-byte is accepted affects timing."])
    code := Impl.MlDsa.AArch64.Sample.rejBoundedWith v.callee
    contract := Spec.MlDsa.rejBoundedContract AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.rejBounded_verifiedWith v
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.expandMaskApi with
    name := Spec.MlDsa.expandMaskApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.expandMaskApi.doc (notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks four coefficients at a time."])
    code := Impl.MlDsa.AArch64.Sample.expandMaskWith v.callee
    contract := Spec.MlDsa.expandMaskContract AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.expandMask_verifiedWith v
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.sampleInBallApi with
    name := Spec.MlDsa.sampleInBallApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.sampleInBallApi.doc (notes := ["SHA3 sampling stops once all coefficients are assigned and squeezes the second block \
      only when needed. Both paths retain the same 272-byte limit and exact failure result."])
    code := Impl.MlDsa.AArch64.Optimized.Ball.selected v.callee
    contract := Spec.MlDsa.sampleInBallContract AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Optimized.Ball.selected_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.MlDsaSample
