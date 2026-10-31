module

public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) verification on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.Arm

def artifacts : List Artifact := [
  Spec.MlDsa.verify44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Verify.verify44
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify44_verified },
  Spec.MlDsa.verify65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Verify.verify65
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify65_verified },
  Spec.MlDsa.verify87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Verify.verify87
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify87_verified }]

end VG.Artifacts.MlDsaVerify.Arm
