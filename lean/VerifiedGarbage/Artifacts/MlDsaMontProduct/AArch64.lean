module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaMontProduct.AArch64

def artifacts : List Artifact := [
  Spec.MlDsa.montProductApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.MontProduct.code
    verified := Proof.MlDsa.AArch64.Optimized.MontProduct.verified }]

end VG.Artifacts.MlDsaMontProduct.AArch64
