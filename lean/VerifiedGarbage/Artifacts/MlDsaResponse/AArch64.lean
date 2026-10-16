module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaResponse.AArch64

def artifacts : List Artifact := [
  Spec.MlDsa.addNormApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.Response.addNorm
    verified := Proof.MlDsa.AArch64.Optimized.Response.addNorm_verified },
  Spec.MlDsa.subLowNormApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
    verified := Proof.MlDsa.AArch64.Optimized.Response.subLowNorm_verified },
  Spec.MlDsa.hintNormApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.Response.hintNorm
    verified := Proof.MlDsa.AArch64.Optimized.Response.hintNorm_verified }]

end VG.Artifacts.MlDsaResponse.AArch64
