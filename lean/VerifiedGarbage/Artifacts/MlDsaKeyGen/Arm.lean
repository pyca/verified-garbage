module

public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) key generation on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaKeyGen.Arm

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
    verified := Proof.MlDsa.Arm.KeyGen.keyGen87_verified }]

end VG.Artifacts.MlDsaKeyGen.Arm
