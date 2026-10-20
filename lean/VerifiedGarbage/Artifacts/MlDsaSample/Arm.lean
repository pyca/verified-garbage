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

/-- The note shared by the four functions. -/
def saveNote : String :=
  "The function saves `r4`–`r11` and its return address in `scratch`; the 8 bytes of stack below the stack \
    pointer hold the stack arguments of the SHA-3 functions it calls."

def artifacts : List Artifact := [
  Spec.MlDsa.rejNTTApi.artifact Arm.target {
    notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them.", saveNote]
    code := Impl.MlDsa.Arm.Sample.rejNTT
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.rejNTT_verified },
  Spec.MlDsa.rejBoundedApi.artifact Arm.target {
    notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of an accepted half-byte is computed \
      without a branch or a table, so only whether each half-byte is accepted affects timing.", saveNote]
    code := Impl.MlDsa.Arm.Sample.rejBounded
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.rejBounded_verified },
  Spec.MlDsa.expandMaskApi.artifact Arm.target {
    notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks them with the loop of \
      `vg_mldsa_bit_unpack`.", saveNote]
    code := Impl.MlDsa.Arm.Sample.expandMask
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.expandMask_verified },
  Spec.MlDsa.sampleInBallApi.artifact Arm.target {
    notes := ["It squeezes 272 bytes of SHAKE256 output (2 blocks) and \
      runs the loop of `SampleInBall` over the 264 after the sign bits.", saveNote]
    code := Impl.MlDsa.Arm.Sample.sampleInBall
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.sampleInBall_verified }]

end VG.Artifacts.MlDsaSample.Arm
