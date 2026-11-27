module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.MlDsa.Arm.Scrub
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlDsa.Arm.PkTr
import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
import VerifiedGarbage.Impl.MlDsa.Arm.Message
import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Verified
import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ML-DSA (FIPS 204) on ARMv7 -/

namespace VG.Artifacts.MlDsa.Arm

open VG

public def artifacts : List (Artifact Arm.target) := [
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
    Spec.MlDsa.preparePublicKey44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparePublic Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.preparePublic "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.prepareSecretKey44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.prepareSecret Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.prepareSecret "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.preparePublicKey65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparePublic Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.preparePublic "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.prepareSecretKey65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.prepareSecret Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.prepareSecret "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.preparePublicKey87Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparePublic Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.Arm.Fn.preparePublic "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) },
    Spec.MlDsa.prepareSecretKey87Api.artifact Arm.target {
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
    Spec.MlDsa.preparedSign44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.signPrepared Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.signPrepared "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.preparedSign65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.signPrepared Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.signPrepared "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.preparedSign87Api.artifact Arm.target {
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
    Spec.MlDsa.preparedSignMessage44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedSignMessage Spec.MlDsa.mlDsa44 "mldsa44"
      verified := Proof.MlDsa.Arm.Fn.preparedSignMessage "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.preparedSignMessage65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedSignMessage Spec.MlDsa.mlDsa65 "mldsa65"
      verified := Proof.MlDsa.Arm.Fn.preparedSignMessage "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.preparedSignMessage87Api.artifact Arm.target {
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
    Spec.MlDsa.preparedVerify44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyPrepared Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.Arm.Fn.verifyPrepared "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.preparedVerify65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyPrepared Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.Arm.Fn.verifyPrepared "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.preparedVerify87Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyPrepared Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.Arm.Fn.verifyPrepared "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) }] ++
  [
    Spec.MlDsa.verifyMessageCached44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyMessageCached Spec.MlDsa.mlDsa44 "mldsa44"
      verified := Proof.MlDsa.Arm.Fn.verifyMessageCached "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.verifyMessageCached65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyMessageCached Spec.MlDsa.mlDsa65 "mldsa65"
      verified := Proof.MlDsa.Arm.Fn.verifyMessageCached "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.verifyMessageCached87Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.verifyMessageCached Spec.MlDsa.mlDsa87 "mldsa87"
      verified := Proof.MlDsa.Arm.Fn.verifyMessageCached "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) },
    Spec.MlDsa.preparedVerifyMessage44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa44 "mldsa44"
      verified := Proof.MlDsa.Arm.Fn.preparedVerifyMessage "mldsa44" "ML-DSA-44" (.inl rfl) },
    Spec.MlDsa.preparedVerifyMessage65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa65 "mldsa65"
      verified := Proof.MlDsa.Arm.Fn.preparedVerifyMessage "mldsa65" "ML-DSA-65" (.inr (.inl rfl)) },
    Spec.MlDsa.preparedVerifyMessage87Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Fn.preparedVerifyMessage Spec.MlDsa.mlDsa87 "mldsa87"
      verified := Proof.MlDsa.Arm.Fn.preparedVerifyMessage "mldsa87" "ML-DSA-87" (.inr (.inr rfl)) }]

spec_apis artifacts

end VG.Artifacts.MlDsa.Arm
