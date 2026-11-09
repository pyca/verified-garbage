module

public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified

public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # ML-DSA (FIPS 204) verification on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.Arm

def artifacts : List Artifact := [
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
    verified := Proof.MlDsa.Arm.Verify.verify87_verified },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact Arm.target {
    code := Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims Spec.MlDsa.mlDsa44
    stack := 52
    verified := Proof.MlDsa.Arm.Message.externalVerify_verified (List.mem_cons_self ..) },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact Arm.target {
    code := Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims Spec.MlDsa.mlDsa65
    stack := 52
    verified := Proof.MlDsa.Arm.Message.externalVerify_verified (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact Arm.target {
    code := Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims Spec.MlDsa.mlDsa87
    stack := 52
    verified := Proof.MlDsa.Arm.Message.externalVerify_verified (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Artifacts.MlDsaVerify.Arm
