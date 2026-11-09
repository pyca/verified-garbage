module

public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.MlDsa.Arm.PkTr
public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
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

-- ML-DSA key-polynomial preparation on 32-bit ARM
namespace VG.Artifacts.MlDsa.Arm.PreparedKey

open VG
open VG.Proof.MlDsa.Arm.Sign (prims)

def artifacts : List Artifact := [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.preparePublic prims Spec.MlDsa.mlDsa44
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.preparePublic_verified (.inl rfl) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.prepareSecret prims Spec.MlDsa.mlDsa44
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.prepareSecret_verified (.inl rfl) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.preparePublic prims Spec.MlDsa.mlDsa65
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.preparePublic_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.prepareSecret prims Spec.MlDsa.mlDsa65
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.prepareSecret_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.preparePublic prims Spec.MlDsa.mlDsa87
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.preparePublic_verified (.inr (.inr rfl)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.PreparedKey.prepareSecret prims Spec.MlDsa.mlDsa87
    stack := 44
    verified := Proof.MlDsa.Arm.PreparedKey.prepareSecret_verified (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsa.Arm.PreparedKey

-- ML-DSA (FIPS 204) signing on 32-bit ARM
namespace VG.Artifacts.MlDsa.Arm.Sign

open VG
open VG.Proof.MlDsa.Arm.Sign (prims)

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa44
    stack := 44
    verified := Proof.MlDsa.Arm.Sign.sign44_verified' },
  Spec.MlDsa.sign65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa65
    stack := 44
    verified := Proof.MlDsa.Arm.Sign.sign65_verified' },
  Spec.MlDsa.sign87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa87
    stack := 44
    verified := Proof.MlDsa.Arm.Sign.sign87_verified' }]

end VG.Artifacts.MlDsa.Arm.Sign

-- ML-DSA (FIPS 204) on 32-bit ARM: signing messages
namespace VG.Artifacts.MlDsa.Arm.SignMessage

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign44Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 52
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign44Fn
      (List.mem_cons_self ..) },
  Spec.MlDsa.signMessage65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign65Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 52
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign65Fn
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  Spec.MlDsa.signMessage87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign87Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 52
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign87Fn
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44")
      (Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedSignMessage_verified
      (Proof.MlDsa.Arm.Message.signPreparedFn (.inl rfl)) (List.mem_cons_self ..) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65")
      (Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedSignMessage_verified
      (Proof.MlDsa.Arm.Message.signPreparedFn (.inr (.inl rfl))) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87")
      (Impl.MlDsa.Arm.Sign.signPrepared Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedSignMessage_verified
      (Proof.MlDsa.Arm.Message.signPreparedFn (.inr (.inr rfl)))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Artifacts.MlDsa.Arm.SignMessage

-- ML-DSA (FIPS 204) on 32-bit ARM: verifying messages with a cached public-key digest
namespace VG.Artifacts.MlDsa.Arm.VerifyMessageCached

open VG

def artifacts : List Artifact := [
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached Spec.MlDsa.verify44Api.name
      Impl.MlDsa.Arm.Verify.verify44 Spec.MlDsa.mlDsa44
    stack := 52
    verified := Proof.MlDsa.Arm.Message.verifyMessageCached44_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached Spec.MlDsa.verify65Api.name
      Impl.MlDsa.Arm.Verify.verify65 Spec.MlDsa.mlDsa65
    stack := 52
    verified := Proof.MlDsa.Arm.Message.verifyMessageCached65_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached Spec.MlDsa.verify87Api.name
      Impl.MlDsa.Arm.Verify.verify87 Spec.MlDsa.mlDsa87
    stack := 52
    verified := Proof.MlDsa.Arm.Message.verifyMessageCached87_verified },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa44")
      (Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedVerifyMessage_verified
      (Proof.MlDsa.Arm.Message.verifyPreparedFn (.inl rfl)) (List.mem_cons_self ..) },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa65")
      (Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedVerifyMessage_verified
      (Proof.MlDsa.Arm.Message.verifyPreparedFn (.inr (.inl rfl))) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa87")
      (Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 52
    verified := Proof.MlDsa.Arm.Message.preparedVerifyMessage_verified
      (Proof.MlDsa.Arm.Message.verifyPreparedFn (.inr (.inr rfl)))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Artifacts.MlDsa.Arm.VerifyMessageCached

namespace VG.Artifacts.MlDsa.Arm

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.KeyGen.keyGen44
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.KeyGen.keyGen65
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.KeyGen.keyGen87
    stack := 36
    verified := Proof.MlDsa.Arm.KeyGen.keyGen87_verified },
  Spec.MlDsa.pkTr44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.PkTr.pkTr Spec.MlDsa.mlDsa44
    stack := 8
    verified := Proof.MlDsa.Arm.PkTr.pkTr44_verified },
  Spec.MlDsa.pkTr65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.PkTr.pkTr Spec.MlDsa.mlDsa65
    stack := 8
    verified := Proof.MlDsa.Arm.PkTr.pkTr65_verified },
  Spec.MlDsa.pkTr87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.PkTr.pkTr Spec.MlDsa.mlDsa87
    stack := 8
    verified := Proof.MlDsa.Arm.PkTr.pkTr87_verified }] ++
  PreparedKey.artifacts ++
  Sign.artifacts ++
  SignMessage.artifacts ++
  [
    Spec.MlDsa.verify44Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Verify.verify44
      stack := 52
      verified := Proof.MlDsa.Arm.Verify.verify44_verified },
    Spec.MlDsa.verify65Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Verify.verify65
      stack := 52
      verified := Proof.MlDsa.Arm.Verify.verify65_verified },
    Spec.MlDsa.verify87Api.artifact Arm.target {
      code := Impl.MlDsa.Arm.Verify.verify87
      stack := 52
      verified := Proof.MlDsa.Arm.Verify.verify87_verified }] ++
  VerifyMessageCached.artifacts

end VG.Artifacts.MlDsa.Arm
