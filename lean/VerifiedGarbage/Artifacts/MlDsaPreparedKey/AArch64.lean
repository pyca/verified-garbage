module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA key-polynomial preparation on AArch64 -/

@[expose] public section

namespace VG.Artifacts.MlDsaPreparedKey.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
    code := Impl.MlDsa.AArch64.PreparedKey.preparePublic Spec.MlDsa.mlDsa44
    stack := 80
    verified := Proof.MlDsa.AArch64.PreparedKey.preparePublic_verified _ (.inl rfl) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
    code := Impl.MlDsa.AArch64.PreparedKey.prepareSecret Spec.MlDsa.mlDsa44
    stack := 80
    verified := Proof.MlDsa.AArch64.PreparedKey.prepareSecret_verified _ (.inl rfl) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
    code := Impl.MlDsa.AArch64.PreparedKey.preparePublic Spec.MlDsa.mlDsa65
    stack := 80
    verified := Proof.MlDsa.AArch64.PreparedKey.preparePublic_verified _ (.inr (.inl rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
    code := Impl.MlDsa.AArch64.PreparedKey.prepareSecret Spec.MlDsa.mlDsa65
    stack := 80
    verified := Proof.MlDsa.AArch64.PreparedKey.prepareSecret_verified _ (.inr (.inl rfl)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
    code := Impl.MlDsa.AArch64.PreparedKey.preparePublic Spec.MlDsa.mlDsa87
    stack := 80
    verified := Proof.MlDsa.AArch64.PreparedKey.preparePublic_verified _ (.inr (.inr rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
    code := Impl.MlDsa.AArch64.PreparedKey.prepareSecret Spec.MlDsa.mlDsa87
    stack := 80
    verified := Proof.MlDsa.AArch64.PreparedKey.prepareSecret_verified _ (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsaPreparedKey.AArch64
