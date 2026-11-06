module

public import VerifiedGarbage.Proof.MlDsa.Arm.PkTr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # ML-DSA (FIPS 204) public-key hash `tr = H(pk, 64)` on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaPkTr.Arm

def artifacts : List Artifact := [
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
    verified := Proof.MlDsa.Arm.PkTr.pkTr87_verified }]

end VG.Artifacts.MlDsaPkTr.Arm
