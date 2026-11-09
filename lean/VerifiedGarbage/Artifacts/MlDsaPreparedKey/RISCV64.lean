module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-DSA key-polynomial preparation on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlDsaPreparedKey.RISCV64

def artifacts : List Artifact := [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PreparedKey.preparePublic Spec.MlDsa.mlDsa44
    stack := 1072
    verified := Proof.MlDsa.RISCV64.PreparedKey.preparePublic44_verified },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PreparedKey.prepareSecret Spec.MlDsa.mlDsa44
    stack := 1072
    verified := Proof.MlDsa.RISCV64.PreparedKey.prepareSecret44_verified },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PreparedKey.preparePublic Spec.MlDsa.mlDsa65
    stack := 1072
    verified := Proof.MlDsa.RISCV64.PreparedKey.preparePublic65_verified },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PreparedKey.prepareSecret Spec.MlDsa.mlDsa65
    stack := 1072
    verified := Proof.MlDsa.RISCV64.PreparedKey.prepareSecret65_verified },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PreparedKey.preparePublic Spec.MlDsa.mlDsa87
    stack := 1072
    verified := Proof.MlDsa.RISCV64.PreparedKey.preparePublic87_verified },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PreparedKey.prepareSecret Spec.MlDsa.mlDsa87
    stack := 1072
    verified := Proof.MlDsa.RISCV64.PreparedKey.prepareSecret87_verified }]

end VG.Artifacts.MlDsaPreparedKey.RISCV64
