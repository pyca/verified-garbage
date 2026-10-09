import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductVerified

namespace VG.Artifacts.MlDsaMontProduct.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.montProductApi with
    target := AArch64.target
    doc := Spec.MlDsa.montProductApi.doc
    code := Impl.MlDsa.AArch64.Optimized.MontProduct.code
    contract := Spec.MlDsa.montProductContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.MontProduct.verified
    spSafe := Code.all_of_forall (fun _=>rfl) _ }]

end VG.Artifacts.MlDsaMontProduct.AArch64
