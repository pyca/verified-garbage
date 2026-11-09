module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.PreparedKey
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ML-DSA key-polynomial preparation on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaPreparedKey.PPC64LE

def artifacts : List Artifact := [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inl rfl) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inl rfl) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inr (.inr rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsaPreparedKey.PPC64LE
