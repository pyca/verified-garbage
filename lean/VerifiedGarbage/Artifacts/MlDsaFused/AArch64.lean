module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Fused internal ML-DSA arithmetic with explicit signed output contracts -/

@[expose] public section

namespace VG.Artifacts.MlDsaFused.AArch64

def artifacts : List Artifact := [
  Spec.MlDsa.multiplyInverseRawApi.artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.productRaw_verified },
  Spec.MlDsa.canonicalizeApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.Response.canonicalize
    verified := Proof.MlDsa.AArch64.Optimized.Response.canonicalize_verified }]

end VG.Artifacts.MlDsaFused.AArch64
