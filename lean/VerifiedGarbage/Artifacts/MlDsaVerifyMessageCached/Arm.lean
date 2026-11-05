module

public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Impl.MlDsa.Arm.Message
public import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
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
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds

/-! # ML-DSA (FIPS 204) on 32-bit ARM: verifying messages with a cached public-key digest -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessageCached.Arm

open VG

def artifacts : List Artifact := [
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached Spec.MlDsa.verify44Api.name
      Impl.MlDsa.Arm.Verify.verify44 Spec.MlDsa.mlDsa44
    stack := 36
    verified := Proof.MlDsa.Arm.Message.verifyMessageCached44_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached Spec.MlDsa.verify65Api.name
      Impl.MlDsa.Arm.Verify.verify65 Spec.MlDsa.mlDsa65
    stack := 36
    verified := Proof.MlDsa.Arm.Message.verifyMessageCached65_verified },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.Message.verifyMessageCached Spec.MlDsa.verify87Api.name
      Impl.MlDsa.Arm.Verify.verify87 Spec.MlDsa.mlDsa87
    stack := 36
    verified := Proof.MlDsa.Arm.Message.verifyMessageCached87_verified }]

end VG.Artifacts.MlDsaVerifyMessageCached.Arm
