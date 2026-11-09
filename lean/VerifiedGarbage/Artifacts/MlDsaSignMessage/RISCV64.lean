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
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage Spec.MlDsa.sign65Api.name
      Impl.MlDsa.RISCV64.Sign.sign65 Spec.MlDsa.mlDsa65
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage Spec.MlDsa.sign87Api.name
      Impl.MlDsa.RISCV64.Sign.sign87 Spec.MlDsa.mlDsa87
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.signMessage87_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44")
      (Impl.MlDsa.RISCV64.Sign.sign44E true) Spec.MlDsa.mlDsa44
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared44_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65")
      (Impl.MlDsa.RISCV64.Sign.sign65E true) Spec.MlDsa.mlDsa65
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared65_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87")
      (Impl.MlDsa.RISCV64.Sign.sign87E true) Spec.MlDsa.mlDsa87
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared87_verified }]

end VG.Artifacts.MlDsaSignMessage.RISCV64
