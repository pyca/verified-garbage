module

public import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.X86.Sample.ExpandMask
public import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop
public import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # ML-DSA (FIPS 204) on x86: the sampling primitives -/

@[expose] public section

namespace VG.Artifacts.MlDsaSample.X86

open VG

def artifacts : List Artifact := [
  Spec.MlDsa.rejNTTApi.artifact X86.target {
    code := Impl.MlDsa.X86.Sample.rejNTT
    stack := 56
    verified := Proof.MlDsa.X86.Sample.RejNtt.verified },
  Spec.MlDsa.rejBoundedApi.artifact X86.target {
    code := Impl.MlDsa.X86.Sample.rejBounded
    stack := 56
    verified := Proof.MlDsa.X86.Sample.RejBounded.verified },
  Spec.MlDsa.expandMaskApi.artifact X86.target {
    code := Impl.MlDsa.X86.Sample.expandMask
    stack := 56
    verified := Proof.MlDsa.X86.Sample.ExpandMask.verified },
  Spec.MlDsa.sampleInBallApi.artifact X86.target {
    code := Impl.MlDsa.X86.Sample.sampleInBall
    stack := 56
    verified := Proof.MlDsa.X86.Sample.Ball.verified }]

end VG.Artifacts.MlDsaSample.X86
