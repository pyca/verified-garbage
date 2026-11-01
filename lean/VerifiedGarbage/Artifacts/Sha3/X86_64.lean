module
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit

public import VerifiedGarbage.Proof.Sha3.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-3 and SHAKE (FIPS 202) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha3.X86_64

def artifacts : List Artifact := [
  Spec.Sha3.absorbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 648 .r9 Impl.Sha3.X86_64.Stream.absorb
    stack := 656
    verified := Proof.Sha3.X86_64.Frame.absorb_framed },
  Spec.Sha3.absorbScratchApi.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Stream.absorb
    stack := 8
    verified := Proof.Sha3.X86_64.Stream.Absorb.absorb_verified },
  Spec.Sha3.padApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 648 .r8 Impl.Sha3.X86_64.Stream.pad
    stack := 656
    verified := Proof.Sha3.X86_64.Frame.pad_framed },
  Spec.Sha3.squeezeApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 648 .r9 Impl.Sha3.X86_64.Stream.squeeze
    stack := 656
    verified := Proof.Sha3.X86_64.Frame.squeeze_framed }]

end VG.Artifacts.Sha3.X86_64
