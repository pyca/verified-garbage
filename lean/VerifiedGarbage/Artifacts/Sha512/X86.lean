module

public import VerifiedGarbage.Proof.Sha512.X86.Shared
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha512.X86.Lit

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha512.X86

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact X86.target {
    code := Impl.Sha512.X86.Stream.init Spec.Sha512.H0_384
    verified := Proof.Sha512.X86.Shared.init Spec.Sha512.H0_384 },
  Spec.Sha512.init512Api.artifact X86.target {
    code := Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512
    verified := Proof.Sha512.X86.Shared.init Spec.Sha512.H0_512 },
  Spec.Sha512.init512_224Api.artifact X86.target {
    code := Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512_224
    verified := Proof.Sha512.X86.Shared.init Spec.Sha512.H0_512_224 },
  Spec.Sha512.init512_256Api.artifact X86.target {
    code := Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512_256
    verified := Proof.Sha512.X86.Shared.init Spec.Sha512.H0_512_256 },
  Spec.Sha512.updateApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 1404 5 Impl.Sha512.X86.Stream.update
    stack := 20 + 1404
    verified := Proof.Sha512.X86.Shared.update },
  Spec.Sha512.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 1400 4 Impl.Sha512.X86.Stream.finalize
    stack := 20 + 1400
    verified := Proof.Sha512.X86.Shared.finalize },
  Spec.Sha512.finalize384Api.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params384)
    stack := 20 + 1400
    verified := Proof.Sha512.X86.Shared.finalize384 },
  Spec.Sha512.finalize512_256Api.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params512_256)
    stack := 20 + 1400
    verified := Proof.Sha512.X86.Shared.finalize512_256 },
  Spec.Sha512.finalize512_224Api.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params512_224)
    stack := 20 + 1400
    verified := Proof.Sha512.X86.Shared.finalize512_224 }]

end VG.Artifacts.Sha512.X86
