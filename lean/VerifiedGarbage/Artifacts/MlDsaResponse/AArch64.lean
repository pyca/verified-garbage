module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaResponse.AArch64

def artifacts : List Artifact := [
  Spec.MlDsa.addNormApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.Response.addNorm
    verified := Proof.MlDsa.AArch64.Optimized.Response.addNorm_verified }]

end VG.Artifacts.MlDsaResponse.AArch64
