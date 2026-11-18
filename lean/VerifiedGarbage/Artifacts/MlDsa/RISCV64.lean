module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Inst

/-! # ML-DSA (FIPS 204) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlDsa.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.keyGen44Reg,
  Spec.MlDsa.keyGen65Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.keyGen65Reg,
  Spec.MlDsa.keyGen87Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.keyGen87Reg,
  Spec.MlDsa.pkTr44Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.pkTr44Reg,
  Spec.MlDsa.pkTr65Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.pkTr65Reg,
  Spec.MlDsa.pkTr87Api.artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.pkTr87Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.preparePublic44Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.prepareSecret44Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.preparePublic65Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.prepareSecret65Reg,
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.preparePublic87Reg,
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target Proof.MlDsa.RISCV64.Scrub.prepareSecret87Reg,
  Spec.MlDsa.sign44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign44
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign44_verified },
  Spec.MlDsa.sign65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign65
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign65_verified },
  Spec.MlDsa.sign87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign87
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign87_verified },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign44E true
    verified := Proof.MlDsa.RISCV64.PreparedKey.signPrepared44_verified },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign65E true
    verified := Proof.MlDsa.RISCV64.PreparedKey.signPrepared65_verified },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign87E true
    verified := Proof.MlDsa.RISCV64.PreparedKey.signPrepared87_verified },
  Spec.MlDsa.signMessage44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage Spec.MlDsa.sign44Api.name
      Impl.MlDsa.RISCV64.Sign.sign44 Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.RISCV64.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage Spec.MlDsa.sign65Api.name
      Impl.MlDsa.RISCV64.Sign.sign65 Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.RISCV64.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage Spec.MlDsa.sign87Api.name
      Impl.MlDsa.RISCV64.Sign.sign87 Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.RISCV64.Message.signMessage87_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44")
      (Impl.MlDsa.RISCV64.Sign.sign44E true) Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared44_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65")
      (Impl.MlDsa.RISCV64.Sign.sign65E true) Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared65_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87")
      (Impl.MlDsa.RISCV64.Sign.sign87E true) Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.RISCV64.Message.signMessagePrepared87_verified },
  Spec.MlDsa.verify44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify44
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify44_verified },
  Spec.MlDsa.verify65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify65
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify65_verified },
  Spec.MlDsa.verify87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify87
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify87_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify44E true
    verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared44_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify65E true
    verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared65_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify87E true
    verified := Proof.MlDsa.RISCV64.PreparedKey.verifyPrepared87_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached Spec.MlDsa.verify44Api.name
      Impl.MlDsa.RISCV64.Verify.verify44 Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached44_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached Spec.MlDsa.verify65Api.name
      Impl.MlDsa.RISCV64.Verify.verify65 Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached65_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached Spec.MlDsa.verify87Api.name
      Impl.MlDsa.RISCV64.Verify.verify87 Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.RISCV64.Message.verifyMessageCached87_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa44")
      (Impl.MlDsa.RISCV64.Verify.verify44E true) Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared44_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa65")
      (Impl.MlDsa.RISCV64.Verify.verify65E true) Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared65_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa87")
      (Impl.MlDsa.RISCV64.Verify.verify87E true) Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.RISCV64.Message.verifyMessagePrepared87_verified }]

end VG.Artifacts.MlDsa.RISCV64
