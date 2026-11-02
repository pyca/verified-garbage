module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on RISC-V: verifying messages -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessage.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.verifyMessage44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessage Spec.MlDsa.verify44Api.name
      Impl.MlDsa.RISCV64.Verify.verify44 Spec.MlDsa.mlDsa44
    stack := 1168
    verified := Proof.MlDsa.RISCV64.Message.verifyMessage44_verified },
  Spec.MlDsa.verifyMessage65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessage Spec.MlDsa.verify65Api.name
      Impl.MlDsa.RISCV64.Verify.verify65 Spec.MlDsa.mlDsa65
    stack := 1168
    verified := Proof.MlDsa.RISCV64.Message.verifyMessage65_verified },
  Spec.MlDsa.verifyMessage87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessage Spec.MlDsa.verify87Api.name
      Impl.MlDsa.RISCV64.Verify.verify87 Spec.MlDsa.mlDsa87
    stack := 1168
    verified := Proof.MlDsa.RISCV64.Message.verifyMessage87_verified }]

end VG.Artifacts.MlDsaVerifyMessage.RISCV64
