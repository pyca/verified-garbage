module

public import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # ML-DSA key-polynomial preparation on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.MlDsaPreparedKey.X86

def artifacts : List Artifact := [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.preparePublic Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.public_verified Proof.MlDsa.X86.Verify.prims_ok (.inl rfl) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.prepareSecret Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.secret_verified Proof.MlDsa.X86.Verify.prims_ok (.inl rfl) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.preparePublic Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.public_verified Proof.MlDsa.X86.Verify.prims_ok (.inr (.inl rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.prepareSecret Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.secret_verified Proof.MlDsa.X86.Verify.prims_ok (.inr (.inl rfl)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.preparePublic Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.public_verified Proof.MlDsa.X86.Verify.prims_ok (.inr (.inr rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.prepareSecret Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.secret_verified Proof.MlDsa.X86.Verify.prims_ok (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsaPreparedKey.X86
