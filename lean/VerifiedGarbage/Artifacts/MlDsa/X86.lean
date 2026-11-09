module

public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlDsa.X86.PkTr
public import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verified
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Final
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
public import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
public import VerifiedGarbage.Proof.MlKem.X86.EncV
public import VerifiedGarbage.Proof.MlKem.X86.NttSetup
public import VerifiedGarbage.Proof.MlKem.X86.Table
public import VerifiedGarbage.Spec.MlDsa.CachedVerify

/-! # ML-DSA (FIPS 204) on x86 -/

@[expose] public section

namespace VG.Artifacts.MlDsa.X86

open VG

open VG.Proof.MlDsa.X86.Sign (prims)

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact X86.target {
    code := Impl.MlDsa.X86.KeyGen.keyGen44
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact X86.target {
    code := Impl.MlDsa.X86.KeyGen.keyGen65
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact X86.target {
    code := Impl.MlDsa.X86.KeyGen.keyGen87
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen87_verified },
  Spec.MlDsa.pkTr44Api.artifact X86.target {
    code := Impl.MlDsa.X86.PkTr.pkTr Spec.MlDsa.mlDsa44
    stack := 56
    verified := Proof.MlDsa.X86.PkTr.pkTr44_verified },
  Spec.MlDsa.pkTr65Api.artifact X86.target {
    code := Impl.MlDsa.X86.PkTr.pkTr Spec.MlDsa.mlDsa65
    stack := 56
    verified := Proof.MlDsa.X86.PkTr.pkTr65_verified },
  Spec.MlDsa.pkTr87Api.artifact X86.target {
    code := Impl.MlDsa.X86.PkTr.pkTr Spec.MlDsa.mlDsa87
    stack := 56
    verified := Proof.MlDsa.X86.PkTr.pkTr87_verified },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.preparePublic Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.public_verified Proof.MlDsa.X86.Verify.prims_ok (.inl rfl) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.prepareSecret Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.secret_verified Proof.MlDsa.X86.Verify.prims_ok (.inl rfl) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.preparePublic Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.public_verified Proof.MlDsa.X86.Verify.prims_ok (.inr (.inl rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.prepareSecret Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.secret_verified Proof.MlDsa.X86.Verify.prims_ok (.inr (.inl rfl)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.preparePublic Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.public_verified Proof.MlDsa.X86.Verify.prims_ok (.inr (.inr rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
    code := Impl.MlDsa.X86.PreparedKey.prepareSecret Impl.MlDsa.X86.Verify.prims Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.X86.PreparedKey.secret_verified Proof.MlDsa.X86.Verify.prims_ok (.inr (.inr rfl)) },
  Spec.MlDsa.sign44Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44")
      (Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa44)
    stack := 136
    verified := Proof.MlDsa.X86.Message.sign44_verified },
  Spec.MlDsa.sign65Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65")
      (Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa65)
    stack := 136
    verified := Proof.MlDsa.X86.Message.sign65_verified },
  Spec.MlDsa.sign87Api.artifact X86.target {
    code := Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87")
      (Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa87)
    stack := 136
    verified := Proof.MlDsa.X86.Message.sign87_verified }] ++
  [
    Spec.MlDsa.signMessage44Api.artifact X86.target {
      code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign44Api.name
        (Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44")
          (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa44)) Spec.MlDsa.mlDsa44
      stack := 176
      verified := Proof.MlDsa.X86.Message.signMessage44_verified },
    (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
      code := Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa44")
        (Impl.MlDsa.X86.Sign.signPrepared Spec.MlDsa.mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44")
          (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa44)) Spec.MlDsa.mlDsa44
      stack := 176
      verified := Proof.MlDsa.X86.Message.signMessagePrepared44_verified },
    Spec.MlDsa.signMessage65Api.artifact X86.target {
      code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign65Api.name
        (Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65")
          (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa65)) Spec.MlDsa.mlDsa65
      stack := 176
      verified := Proof.MlDsa.X86.Message.signMessage65_verified },
    (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
      code := Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa65")
        (Impl.MlDsa.X86.Sign.signPrepared Spec.MlDsa.mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65")
          (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa65)) Spec.MlDsa.mlDsa65
      stack := 176
      verified := Proof.MlDsa.X86.Message.signMessagePrepared65_verified },
    Spec.MlDsa.signMessage87Api.artifact X86.target {
      code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign87Api.name
        (Impl.MlDsa.X86.Sign.signEntry Spec.MlDsa.mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87")
          (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa87)) Spec.MlDsa.mlDsa87
      stack := 176
      verified := Proof.MlDsa.X86.Message.signMessage87_verified },
    (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
      code := Impl.MlDsa.X86.Message.signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa87")
        (Impl.MlDsa.X86.Sign.signPrepared Spec.MlDsa.mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87")
          (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa87)) Spec.MlDsa.mlDsa87
      stack := 176
      verified := Proof.MlDsa.X86.Message.signMessagePrepared87_verified }] ++
  [
    Spec.MlDsa.verify44Api.artifact X86.target {
      code := Impl.MlDsa.X86.Verify.verify44
      stack := 136
      verified := Proof.MlDsa.X86.Message.verify44_verified },
    Spec.MlDsa.verify65Api.artifact X86.target {
      code := Impl.MlDsa.X86.Verify.verify65
      stack := 136
      verified := Proof.MlDsa.X86.Message.verify65_verified },
    Spec.MlDsa.verify87Api.artifact X86.target {
      code := Impl.MlDsa.X86.Verify.verify87
      stack := 136
      verified := Proof.MlDsa.X86.Message.verify87_verified }] ++
  [
    (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
      code := Impl.MlDsa.X86.Message.verifyMessageCached Spec.MlDsa.verify44Api.name
        Impl.MlDsa.X86.Verify.verify44 Spec.MlDsa.mlDsa44
      stack := 172
      verified := Proof.MlDsa.X86.Message.verifyMessageCached44_verified },
    (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86.target {
      code := Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.preparedName "mldsa44")
        (Impl.MlDsa.X86.Verify.verifyPreparedOf Spec.MlDsa.mlDsa44 "mldsa44") Spec.MlDsa.mlDsa44
      stack := 172
      verified := Proof.MlDsa.X86.Message.verifyMessagePrepared44_verified },
    (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
      code := Impl.MlDsa.X86.Message.verifyMessageCached Spec.MlDsa.verify65Api.name
        Impl.MlDsa.X86.Verify.verify65 Spec.MlDsa.mlDsa65
      stack := 172
      verified := Proof.MlDsa.X86.Message.verifyMessageCached65_verified },
    (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86.target {
      code := Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.preparedName "mldsa65")
        (Impl.MlDsa.X86.Verify.verifyPreparedOf Spec.MlDsa.mlDsa65 "mldsa65") Spec.MlDsa.mlDsa65
      stack := 172
      verified := Proof.MlDsa.X86.Message.verifyMessagePrepared65_verified },
    (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
      code := Impl.MlDsa.X86.Message.verifyMessageCached Spec.MlDsa.verify87Api.name
        Impl.MlDsa.X86.Verify.verify87 Spec.MlDsa.mlDsa87
      stack := 172
      verified := Proof.MlDsa.X86.Message.verifyMessageCached87_verified },
    (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86.target {
      code := Impl.MlDsa.X86.Message.verifyMessageCached (Impl.MlDsa.X86.Verify.preparedName "mldsa87")
        (Impl.MlDsa.X86.Verify.verifyPreparedOf Spec.MlDsa.mlDsa87 "mldsa87") Spec.MlDsa.mlDsa87
      stack := 172
      verified := Proof.MlDsa.X86.Message.verifyMessagePrepared87_verified }]

end VG.Artifacts.MlDsa.X86
