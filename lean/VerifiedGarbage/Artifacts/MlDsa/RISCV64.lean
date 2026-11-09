module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PkTr
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Inst

/-! # ML-DSA (FIPS 204) on RISC-V (RV64) -/

@[expose] public section

namespace VG.Artifacts.MlDsa.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.KeyGen.keyGen44
    stack := 1168
    verified := Proof.MlDsa.RISCV64.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.KeyGen.keyGen65
    stack := 1168
    verified := Proof.MlDsa.RISCV64.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.KeyGen.keyGen87
    stack := 1168
    verified := Proof.MlDsa.RISCV64.KeyGen.keyGen87_verified },
  Spec.MlDsa.pkTr44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PkTr.pkTr Spec.MlDsa.mlDsa44
    stack := 1168
    verified := Proof.MlDsa.RISCV64.PkTr.pkTr44_verified },
  Spec.MlDsa.pkTr65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PkTr.pkTr Spec.MlDsa.mlDsa65
    stack := 1168
    verified := Proof.MlDsa.RISCV64.PkTr.pkTr65_verified },
  Spec.MlDsa.pkTr87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PkTr.pkTr Spec.MlDsa.mlDsa87
    stack := 1168
    verified := Proof.MlDsa.RISCV64.PkTr.pkTr87_verified },
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
    verified := Proof.MlDsa.RISCV64.PreparedKey.prepareSecret87_verified },
  Spec.MlDsa.sign44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign44
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign44_verified },
  Spec.MlDsa.sign65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign65
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign65_verified },
  Spec.MlDsa.sign87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign87
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign87_verified },
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
    verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared87_verified },
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

end VG.Artifacts.MlDsa.RISCV64
