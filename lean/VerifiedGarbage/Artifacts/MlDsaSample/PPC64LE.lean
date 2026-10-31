module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.ExpandMask
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.BallCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on PPC64LE: the sampling primitives -/

@[expose] public section

namespace VG.Artifacts.MlDsaSample.PPC64LE

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.rejNTTApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sample.rejNTT
    stack := 48
    verified := Proof.MlDsa.PPC64LE.Sample.rejNTT_verified },
  Spec.MlDsa.rejBoundedApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sample.rejBounded
    stack := 48
    verified := Proof.MlDsa.PPC64LE.Sample.rejBounded_verified },
  Spec.MlDsa.expandMaskApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sample.expandMask
    stack := 48
    verified := Proof.MlDsa.PPC64LE.Sample.expandMask_verified },
  Spec.MlDsa.sampleInBallApi.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sample.sampleInBall
    stack := 48
    verified := Proof.MlDsa.PPC64LE.Sample.sampleInBall_verified }]

end VG.Artifacts.MlDsaSample.PPC64LE
