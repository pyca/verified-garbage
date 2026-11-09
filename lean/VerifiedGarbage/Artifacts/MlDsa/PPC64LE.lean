module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.PkTr
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inst

/-! # ML-DSA (FIPS 204) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsa.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen87_verified },
  Spec.MlDsa.pkTr44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa44
    stack := 48
    verified := Proof.MlDsa.PPC64LE.PkTr.pkTr44_verified },
  Spec.MlDsa.pkTr65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa65
    stack := 48
    verified := Proof.MlDsa.PPC64LE.PkTr.pkTr65_verified },
  Spec.MlDsa.pkTr87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa87
    stack := 48
    verified := Proof.MlDsa.PPC64LE.PkTr.pkTr87_verified },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inl rfl) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inl rfl) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.preparePublic Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.preparePublic_verified (.inr (.inr rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PreparedKey.prepareSecret Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.PreparedKey.prepareSecret_verified (.inr (.inr rfl)) },
  Spec.MlDsa.sign44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.sign44_verified },
  Spec.MlDsa.sign65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.sign65_verified },
  Spec.MlDsa.sign87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.sign87_verified },
  Spec.MlDsa.signMessage44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign44Api.name
      Impl.MlDsa.PPC64LE.Sign.sign44 Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign65Api.name
      Impl.MlDsa.PPC64LE.Sign.sign65 Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign87Api.name
      Impl.MlDsa.PPC64LE.Sign.sign87 Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.signMessage87_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44")
      Impl.MlDsa.PPC64LE.Sign.signPrepared44 Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedSignMessage44_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65")
      Impl.MlDsa.PPC64LE.Sign.signPrepared65 Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedSignMessage65_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87")
      Impl.MlDsa.PPC64LE.Sign.signPrepared87 Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedSignMessage87_verified },
  Spec.MlDsa.verify44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verify44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Verify.verify44_verified },
  Spec.MlDsa.verify65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verify65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Verify.verify65_verified },
  Spec.MlDsa.verify87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verify87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Verify.verify87_verified },
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

end VG.Artifacts.MlDsa.PPC64LE
