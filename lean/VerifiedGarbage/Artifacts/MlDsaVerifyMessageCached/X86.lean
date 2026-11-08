module

public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
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
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
public import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
public import VerifiedGarbage.Proof.MlKem.X86.EncV
public import VerifiedGarbage.Proof.MlKem.X86.NttSetup
public import VerifiedGarbage.Proof.MlKem.X86.Table
public import VerifiedGarbage.TCB.X86.Print

/-! # ML-DSA (FIPS 204) on x86 (32-bit): verifying messages with a cached public-key digest, with encoded and prepared keys -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessageCached.X86

open VG

def artifacts : List Artifact := [
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

end VG.Artifacts.MlDsaVerifyMessageCached.X86
