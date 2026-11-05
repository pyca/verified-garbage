module

public import VerifiedGarbage.Proof.Sha512.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha512.Arm

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_384
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_384 },
  Spec.Sha512.init512Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512 },
  Spec.Sha512.init512_224Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_224
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_224 },
  Spec.Sha512.init512_256Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_256
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_256 },
  Spec.Sha512.updateApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 1392 2 Impl.Sha512.Arm.Stream.update
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.update },
  Spec.Sha512.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 1392 1 Impl.Sha512.Arm.Stream.finalize
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.finalize },
  Spec.Sha512.finalize384Api.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params384)
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.finalize384 },
  Spec.Sha512.finalize512_256Api.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_256)
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.finalize512_256 },
  Spec.Sha512.finalize512_224Api.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_224)
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.finalize512_224 },
  Spec.Sha512.digest384Api.artifact Arm.target {
    code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha384H
    stack := 16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha384H
    verified := Proof.MdStream.Arm.Digest.sha384_digest },
  Spec.Sha512.digest512Api.artifact Arm.target {
    code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H'
    stack := 16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512H'
    verified := Proof.MdStream.Arm.Digest.sha512_digest },
  Spec.Sha512.digest512_224Api.artifact Arm.target {
    code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_224H
    stack := 16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512_224H
    verified := Proof.MdStream.Arm.Digest.sha512_224_digest },
  Spec.Sha512.digest512_256Api.artifact Arm.target {
    code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_256H
    stack := 16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512_256H
    verified := Proof.MdStream.Arm.Digest.sha512_256_digest }]

end VG.Artifacts.Sha512.Arm
