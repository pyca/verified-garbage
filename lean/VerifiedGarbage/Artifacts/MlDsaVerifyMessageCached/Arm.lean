module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
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
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.TCB.Arm.Print

/-! # ML-DSA (FIPS 204) on 32-bit ARM: verifying messages with a cached public-key digest -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessageCached.Arm

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

end VG.Artifacts.MlDsaVerifyMessageCached.Arm
