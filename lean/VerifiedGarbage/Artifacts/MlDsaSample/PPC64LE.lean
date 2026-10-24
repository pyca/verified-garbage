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

/-- The note shared by the four functions. -/
def saveNote : String :=
  "The function has no stack frame of its own: it saves `r27`–`r31` and its return address in `scratch`; \
    the SHA-3 functions it calls use the 48 bytes of stack below the stack pointer."

def artifacts : List Artifact := [
  Spec.MlDsa.rejNTTApi.artifact PPC64LE.target {
    notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them.", saveNote]
    code := Impl.MlDsa.PPC64LE.Sample.rejNTT
    stack := 48
    verified := Proof.MlDsa.PPC64LE.Sample.rejNTT_verified },
  Spec.MlDsa.rejBoundedApi.artifact PPC64LE.target {
    notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of an accepted half-byte is computed \
      without a branch or a table, so only whether each half-byte is accepted affects timing.", saveNote]
    code := Impl.MlDsa.PPC64LE.Sample.rejBounded
    stack := 48
    verified := Proof.MlDsa.PPC64LE.Sample.rejBounded_verified },
  Spec.MlDsa.expandMaskApi.artifact PPC64LE.target {
    notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks them with the loop of \
      `vg_mldsa_bit_unpack`.", saveNote]
    code := Impl.MlDsa.PPC64LE.Sample.expandMask
    stack := 48
    verified := Proof.MlDsa.PPC64LE.Sample.expandMask_verified },
  Spec.MlDsa.sampleInBallApi.artifact PPC64LE.target {
    notes := ["It squeezes 272 bytes of SHAKE256 output (2 blocks) and \
      runs the loop of `SampleInBall` over the 264 after the sign bits.", saveNote]
    code := Impl.MlDsa.PPC64LE.Sample.sampleInBall
    stack := 48
    verified := Proof.MlDsa.PPC64LE.Sample.sampleInBall_verified }]

end VG.Artifacts.MlDsaSample.PPC64LE
