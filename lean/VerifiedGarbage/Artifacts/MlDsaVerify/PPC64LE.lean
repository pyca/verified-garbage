module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ML-DSA (FIPS 204) verification on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.PPC64LE

def artifacts : List Artifact := [
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
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verifyPrepared44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Verify.verifyPrepared44_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verifyPrepared65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Verify.verifyPrepared65_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verifyPrepared87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Verify.verifyPrepared87_verified }]

end VG.Artifacts.MlDsaVerify.PPC64LE
