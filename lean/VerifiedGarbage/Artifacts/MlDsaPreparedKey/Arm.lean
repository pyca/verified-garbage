module

public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # ML-DSA key-polynomial preparation on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaPreparedKey.Arm

open VG
open VG.Proof.MlDsa.Arm.Sign (prims)

def artifacts : List Artifact := [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.preparePublic prims Spec.MlDsa.mlDsa44
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.preparePublic_verified (.inl rfl) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.prepareSecret prims Spec.MlDsa.mlDsa44
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.prepareSecret_verified (.inl rfl) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.preparePublic prims Spec.MlDsa.mlDsa65
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.preparePublic_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.prepareSecret prims Spec.MlDsa.mlDsa65
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.prepareSecret_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.preparePublic prims Spec.MlDsa.mlDsa87
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.preparePublic_verified (.inr (.inr rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.prepareSecret prims Spec.MlDsa.mlDsa87
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.prepareSecret_verified (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsaPreparedKey.Arm
