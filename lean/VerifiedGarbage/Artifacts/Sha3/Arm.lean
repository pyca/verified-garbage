module

public import VerifiedGarbage.Proof.Sha3.Arm.Shared
public import VerifiedGarbage.Proof.Sha3.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-3 and SHAKE (FIPS 202) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.Sha3.Arm

def artifacts : List Artifact := [
  Spec.Sha3.permuteApi.artifact Arm.target {
    code := Impl.Sha3.Arm.permute
    verified := Proof.Sha3.Arm.Shared.permute },
  Spec.Sha3.absorbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 656 1 Impl.Sha3.Arm.Stream.absorb
    stack := 656
    verified := Proof.Sha3.Arm.Frame.absorb_framed },
  Spec.Sha3.absorbScratchApi.artifact Arm.target {
    code := Impl.Sha3.Arm.Stream.absorb
    verified := Proof.Sha3.Arm.Shared.absorb },
  Spec.Sha3.padApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 656 0 Impl.Sha3.Arm.Stream.pad
    stack := 656
    verified := Proof.Sha3.Arm.Frame.pad_framed },
  Spec.Sha3.padScratchApi.artifact Arm.target {
    code := Impl.Sha3.Arm.Stream.pad
    verified := Proof.Sha3.Arm.Shared.pad },
  Spec.Sha3.squeezeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 656 1 Impl.Sha3.Arm.Stream.squeeze
    stack := 656
    verified := Proof.Sha3.Arm.Frame.squeeze_framed },
  Spec.Sha3.squeezeScratchApi.artifact Arm.target {
    code := Impl.Sha3.Arm.Stream.squeeze
    verified := Proof.Sha3.Arm.Shared.squeeze }]

end VG.Artifacts.Sha3.Arm
