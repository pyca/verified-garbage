module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-DSA (FIPS 204) on RISC-V: signing messages -/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage Spec.MlDsa.sign44Api.name
      Impl.MlDsa.RISCV64.Sign.sign44 Spec.MlDsa.mlDsa44
    stack := 1168
    verified := Proof.MlDsa.RISCV64.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage Spec.MlDsa.sign65Api.name
      Impl.MlDsa.RISCV64.Sign.sign65 Spec.MlDsa.mlDsa65
    stack := 1168
    verified := Proof.MlDsa.RISCV64.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage Spec.MlDsa.sign87Api.name
      Impl.MlDsa.RISCV64.Sign.sign87 Spec.MlDsa.mlDsa87
    stack := 1168
    verified := Proof.MlDsa.RISCV64.Message.signMessage87_verified }]

end VG.Artifacts.MlDsaSignMessage.RISCV64
