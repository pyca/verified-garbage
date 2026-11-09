module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-DSA (FIPS 204) on RISC-V: verifying messages with a cached public-key digest -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessageCached.RISCV64

def artifacts : List Artifact := [
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached Spec.MlDsa.verify44Api.name
      Impl.MlDsa.RISCV64.Verify.verify44 Spec.MlDsa.mlDsa44
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached44_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached Spec.MlDsa.verify65Api.name
      Impl.MlDsa.RISCV64.Verify.verify65 Spec.MlDsa.mlDsa65
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached65_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached Spec.MlDsa.verify87Api.name
      Impl.MlDsa.RISCV64.Verify.verify87 Spec.MlDsa.mlDsa87
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached87_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa44")
      (Impl.MlDsa.RISCV64.Verify.verify44E true) Spec.MlDsa.mlDsa44
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared44_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa65")
      (Impl.MlDsa.RISCV64.Verify.verify65E true) Spec.MlDsa.mlDsa65
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared65_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa87")
      (Impl.MlDsa.RISCV64.Verify.verify87E true) Spec.MlDsa.mlDsa87
    stack := 1184
    verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared87_verified }]

end VG.Artifacts.MlDsaVerifyMessageCached.RISCV64
