module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ML-DSA (FIPS 204) on PPC64LE: verifying messages with a cached public-key digest, with encoded or prepared public keys -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessageCached.PPC64LE

def artifacts : List Artifact := [
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached Spec.MlDsa.verify44Api.name
      Impl.MlDsa.PPC64LE.Verify.verify44 Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessageCached44_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached Spec.MlDsa.verify65Api.name
      Impl.MlDsa.PPC64LE.Verify.verify65 Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessageCached65_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached Spec.MlDsa.verify87Api.name
      Impl.MlDsa.PPC64LE.Verify.verify87 Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessageCached87_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa44")
      Impl.MlDsa.PPC64LE.Verify.verifyPrepared44 Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedVerifyMessage44_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa65")
      Impl.MlDsa.PPC64LE.Verify.verifyPrepared65 Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedVerifyMessage65_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa87")
      Impl.MlDsa.PPC64LE.Verify.verifyPrepared87 Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedVerifyMessage87_verified }]

end VG.Artifacts.MlDsaVerifyMessageCached.PPC64LE
