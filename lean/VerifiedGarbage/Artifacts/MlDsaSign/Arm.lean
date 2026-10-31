module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks

/-! # ML-DSA (FIPS 204) signing on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.Arm

open VG
open VG.Proof.MlDsa.Arm.Sign (prims)

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa44
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign44_verified' },
  Spec.MlDsa.sign65Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa65
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign65_verified' },
  Spec.MlDsa.sign87Api.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa87
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign87_verified' }]

end VG.Artifacts.MlDsaSign.Arm
