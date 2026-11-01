module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Permute
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-3 and SHAKE (FIPS 202) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha3.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha3.absorbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r8 Impl.Sha3.PPC64LE.Stream.absorb
    stack := 48 + 672
    verified := Proof.Sha3.PPC64LE.Frame.absorb_framed },
  Spec.Sha3.absorbScratchApi.artifact PPC64LE.target {
    code := Impl.Sha3.PPC64LE.Stream.absorb
    stack := 48
    verified := Proof.Sha3.PPC64LE.Stream.absorb_verified },
  Spec.Sha3.padApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r7 Impl.Sha3.PPC64LE.Stream.pad
    stack := 48 + 672
    verified := Proof.Sha3.PPC64LE.Frame.pad_framed },
  Spec.Sha3.squeezeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 672 .r8 Impl.Sha3.PPC64LE.Stream.squeeze
    stack := 48 + 672
    verified := Proof.Sha3.PPC64LE.Frame.squeeze_framed }]

end VG.Artifacts.Sha3.PPC64LE
