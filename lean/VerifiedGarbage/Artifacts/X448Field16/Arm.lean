module

public import VerifiedGarbage.Proof.X448.Arm.FnVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Arithmetic in curve448's field, in radix `2^16`, on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X448Field16.Arm

open VG.Spec.X448.Field16 VG.Impl.X448.Arm VG.Proof.X448.Arm

def artifacts : List Artifact := [
  mulApi.artifact Arm.target {
    code := mulFn
    verified := gf448_mul_verified },
  addApi.artifact Arm.target {
    code := addFn
    verified := gf448_add_verified },
  subApi.artifact Arm.target {
    code := subFn
    verified := gf448_sub_verified },
  mulA24Api.artifact Arm.target {
    code := mulA24Fn
    verified := gf448_mulA24_verified }]

end VG.Artifacts.X448Field16.Arm
