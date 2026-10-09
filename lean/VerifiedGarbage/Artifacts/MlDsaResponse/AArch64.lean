import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVerified

namespace VG.Artifacts.MlDsaResponse.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.addNormApi with
    target := AArch64.target
    doc := Spec.MlDsa.addNormApi.doc
    code := Impl.MlDsa.AArch64.Optimized.Response.addNorm
    contract := Spec.MlDsa.addNormContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.Response.addNorm_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.addNormContract; rfl⟩ },
  { Spec.MlDsa.subLowNormApi with
    target := AArch64.target
    doc := Spec.MlDsa.subLowNormApi.doc
    code := Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
    contract := Spec.MlDsa.subLowNormContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.Response.subLowNorm_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.subLowNormContract; rfl⟩ },
  { Spec.MlDsa.hintNormApi with
    target := AArch64.target
    doc := Spec.MlDsa.hintNormApi.doc
    code := Impl.MlDsa.AArch64.Optimized.Response.hintNorm
    contract := Spec.MlDsa.hintNormContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.Response.hintNorm_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.hintNormContract; rfl⟩ }]

end VG.Artifacts.MlDsaResponse.AArch64
