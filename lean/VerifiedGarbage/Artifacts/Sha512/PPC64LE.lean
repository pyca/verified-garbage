module

public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Shared

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha512.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_384
    verified := Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_384 },
  Spec.Sha512.init512Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512
    verified := Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512 },
  Spec.Sha512.init512_224Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512_224
    verified := Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512_224 },
  Spec.Sha512.init512_256Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512_256
    verified := Proof.Sha512.PPC64LE.Shared.init Spec.Sha512.H0_512_256 },
  Spec.Sha512.updateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r7 Impl.Sha512.PPC64LE.Stream.update
    stack := 1408
    verified := Proof.Sha512.PPC64LE.Shared.update },
  Spec.Sha512.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize
    stack := 1408
    verified := Proof.Sha512.PPC64LE.Shared.finalize },
  Spec.Sha512.finalize384Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize384
    stack := 1408
    verified := Proof.Sha512.PPC64LE.Shared.finalize384 },
  Spec.Sha512.finalize512_256Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_256
    stack := 1408
    verified := Proof.Sha512.PPC64LE.Shared.finalize512_256 },
  Spec.Sha512.finalize512_224Api.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_224
    stack := 1408
    verified := Proof.Sha512.PPC64LE.Shared.finalize512_224 }]

end VG.Artifacts.Sha512.PPC64LE
