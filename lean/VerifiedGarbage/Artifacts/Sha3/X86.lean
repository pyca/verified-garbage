module

public import VerifiedGarbage.Proof.Sha3.X86.Shared
public import VerifiedGarbage.Proof.Sha3.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # SHA-3 and SHAKE (FIPS 202) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha3.X86

def artifacts : List Artifact := [
  Spec.Sha3.absorbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 668 5 Impl.Sha3.X86.Stream.absorb
    stack := 680
    verified := Proof.Sha3.X86.Frame.absorb_framed },
  Spec.Sha3.absorbScratchApi.artifact X86.target {
    code := Impl.Sha3.X86.Stream.absorb
    stack := 12
    verified := Proof.Sha3.X86.Shared.absorb },
  Spec.Sha3.padApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 664 4 Impl.Sha3.X86.Stream.pad
    stack := 676
    verified := Proof.Sha3.X86.Frame.pad_framed },
  Spec.Sha3.squeezeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 668 5 Impl.Sha3.X86.Stream.squeeze
    stack := 680
    verified := Proof.Sha3.X86.Frame.squeeze_framed }]

end VG.Artifacts.Sha3.X86
