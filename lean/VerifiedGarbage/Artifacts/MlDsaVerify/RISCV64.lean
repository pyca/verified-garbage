module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-DSA (FIPS 204) verification on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.verify44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify44
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify44_verified },
  Spec.MlDsa.verify65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify65
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify65_verified },
  Spec.MlDsa.verify87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify87
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify87_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify44E true
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared44_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify65E true
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared65_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify87E true
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared87_verified }]

end VG.Artifacts.MlDsaVerify.RISCV64
