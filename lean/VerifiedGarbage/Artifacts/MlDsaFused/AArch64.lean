import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified

/-! Fused internal ML-DSA arithmetic with explicit signed output contracts. -/
namespace VG.Artifacts.MlDsaFused.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.multiplyInverseRawApi with
    target := AArch64.target
    doc := Spec.MlDsa.multiplyInverseRawApi.doc
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true
    contract := Spec.MlDsa.multiplyInverseRawContract
      (AArch64.abi.withConsts Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts)
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.productRaw_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.multiplyInverseRawContract; rfl⟩ },
  { Spec.MlDsa.canonicalizeApi with
    target := AArch64.target
    doc := Spec.MlDsa.canonicalizeApi.doc
    code := Impl.MlDsa.AArch64.Optimized.Response.canonicalize
    contract := Spec.MlDsa.canonicalizeContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Optimized.Response.canonicalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.canonicalizeContract; rfl⟩ }]

end VG.Artifacts.MlDsaFused.AArch64
