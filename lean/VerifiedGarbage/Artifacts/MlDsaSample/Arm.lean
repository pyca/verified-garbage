module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.ExpandMask
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on 32-bit ARM: the sampling primitives -/

@[expose] public section

namespace VG.Artifacts.MlDsaSample.Arm

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.rejNTTApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sample.rejNTT
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.rejNTT_verified },
  Spec.MlDsa.rejBoundedApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sample.rejBounded
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.rejBounded_verified },
  Spec.MlDsa.expandMaskApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sample.expandMask
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.expandMask_verified },
  Spec.MlDsa.sampleInBallApi.artifact Arm.target {
    code := Impl.MlDsa.Arm.Sample.sampleInBall
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.sampleInBall_verified }]

end VG.Artifacts.MlDsaSample.Arm
