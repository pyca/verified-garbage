module

public import VerifiedGarbage.Proof.X448.Arm.Verified
public import VerifiedGarbage.Proof.X448.Arm.Exchange
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # X448 (RFC 7748) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.X448.Arm

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact Arm.target {
    code := Impl.X448.Arm.x448
    verified := Proof.X448.Arm.x448_verified },
  Spec.X448.exchangeApi.artifact Arm.target {
    code := Impl.Xdh.Arm.exchange "vg_x448" Impl.X448.Arm.x448 56
    stack := 8
    verified := Proof.X448.Arm.Exchange.exchange_baseline },
  Spec.X448.x448BaseApi.artifact Arm.target {
    code := Impl.X448.Arm.x448Base
    verified := Proof.X448.Arm.x448Base_verified }]

end VG.Artifacts.X448.Arm
