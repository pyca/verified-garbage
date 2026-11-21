module

public import VerifiedGarbage.Proof.MlDsa.Arm.Scrub
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.MlDsa.Arm.PkTr
public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Verified
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst

/-! # ML-DSA (FIPS 204) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.MlDsa.Arm

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Fn.keyGen Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.Arm.Fn.keyGen "mldsa44" "ML-DSA-44" (.inl rfl) },
  Spec.MlDsa.keyGen65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Fn.keyGen Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.Arm.Fn.keyGen "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
  Spec.MlDsa.keyGen87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Fn.keyGen Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.Arm.Fn.keyGen "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) },
  Spec.MlDsa.pkTr44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Fn.pkTr Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.Arm.Fn.pkTr "mldsa44" "ML-DSA-44" (.inl rfl) },
  Spec.MlDsa.pkTr65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Fn.pkTr Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.Arm.Fn.pkTr "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
  Spec.MlDsa.pkTr87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Fn.pkTr Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.Arm.Fn.pkTr "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) }] ++
  [
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparePublic Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.preparePublic "mldsa44" "ML-DSA-44" (.inl rfl) },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.prepareSecret Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.prepareSecret "mldsa44" "ML-DSA-44" (.inl rfl) },
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparePublic Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.preparePublic "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.prepareSecret Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.prepareSecret "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparePublic Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.Arm.Fn.preparePublic "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.prepareSecret Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.Arm.Fn.prepareSecret "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) }] ++
  [
    Spec.MlDsa.sign44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.sign Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.sign "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.sign65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.sign Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.sign "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.sign87Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.sign Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.Arm.Fn.sign "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) },
    (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.signPrepared Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.signPrepared "mldsa44" "ML-DSA-44" (.inl rfl) },
    (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.signPrepared Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.signPrepared "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.signPrepared Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.Arm.Fn.signPrepared "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) }] ++
  [
    Spec.MlDsa.signMessage44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.signMessage Spec.MlDsa.mlDsa44 "mldsa44"
      verified := Proof.MlDsa.Arm.Fn.signMessage "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.signMessage65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.signMessage Spec.MlDsa.mlDsa65 "mldsa65"
      verified := Proof.MlDsa.Arm.Fn.signMessage "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.signMessage87Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.signMessage Spec.MlDsa.mlDsa87 "mldsa87"
      verified := Proof.MlDsa.Arm.Fn.signMessage "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) },
    (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedSignMessage Spec.MlDsa.mlDsa44 "mldsa44"
      verified := Proof.MlDsa.Arm.Fn.preparedSignMessage "mldsa44" "ML-DSA-44" (.inl rfl) },
    (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedSignMessage Spec.MlDsa.mlDsa65 "mldsa65"
      verified := Proof.MlDsa.Arm.Fn.preparedSignMessage "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedSignMessage Spec.MlDsa.mlDsa87 "mldsa87"
      verified := Proof.MlDsa.Arm.Fn.preparedSignMessage "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) }] ++
  [
    Spec.MlDsa.verify44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verify Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.verify "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.verify65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verify Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.verify "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.verify87Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verify Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.Arm.Fn.verify "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) },
    (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyPrepared Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.verifyPrepared "mldsa44" "ML-DSA-44" (.inl rfl) },
    (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyPrepared Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.verifyPrepared "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyPrepared Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.Arm.Fn.verifyPrepared "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) }] ++
  [
    (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyMessageCached Spec.MlDsa.mlDsa44 "mldsa44"
      verified := Proof.MlDsa.Arm.Fn.verifyMessageCached "mldsa44" "ML-DSA-44" (.inl rfl) },
    (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyMessageCached Spec.MlDsa.mlDsa65 "mldsa65"
      verified := Proof.MlDsa.Arm.Fn.verifyMessageCached "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyMessageCached Spec.MlDsa.mlDsa87 "mldsa87"
      verified := Proof.MlDsa.Arm.Fn.verifyMessageCached "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) },
    (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa44 "mldsa44"
      verified := Proof.MlDsa.Arm.Fn.preparedVerifyMessage "mldsa44" "ML-DSA-44" (.inl rfl) },
    (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa65 "mldsa65"
      verified := Proof.MlDsa.Arm.Fn.preparedVerifyMessage "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa87 "mldsa87"
      verified := Proof.MlDsa.Arm.Fn.preparedVerifyMessage "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsa.Arm
