module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact Arm.target {
    consts := Impl.Ed25519.Arm.combConsts
    code := Impl.Ed25519.Arm.scalarBase
    verified := Proof.Ed25519.Arm.scalarBase_verified
    stack := 0 }]

end VG.Artifacts.Ed25519ScalarBase.Arm
