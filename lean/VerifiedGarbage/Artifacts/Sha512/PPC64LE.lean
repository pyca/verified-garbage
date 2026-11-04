module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
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
    verified := Proof.Sha512.PPC64LE.Shared.finalize512_224 },
  Spec.Sha512.digest384Api.artifact PPC64LE.target {
    code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha384.hash
    stack := 96 + Impl.MdStream.PPC64LE.Digest.frameBytes Proof.Hmac.Stream.PPC64LE.Sha384.hash
    verified := Proof.Hmac.Stream.PPC64LE.Sha384.digest },
  Spec.Sha512.digest512Api.artifact PPC64LE.target {
    code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha512.hash
    stack := 96 + Impl.MdStream.PPC64LE.Digest.frameBytes Proof.Hmac.Stream.PPC64LE.Sha512.hash
    verified := Proof.Hmac.Stream.PPC64LE.Sha512.digest },
  Spec.Sha512.digest512_224Api.artifact PPC64LE.target {
    code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha512_224.hash
    stack := 96 + Impl.MdStream.PPC64LE.Digest.frameBytes Proof.Hmac.Stream.PPC64LE.Sha512_224.hash
    verified := Proof.Hmac.Stream.PPC64LE.Sha512_224.digest },
  Spec.Sha512.digest512_256Api.artifact PPC64LE.target {
    code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha512_256.hash
    stack := 96 + Impl.MdStream.PPC64LE.Digest.frameBytes Proof.Hmac.Stream.PPC64LE.Sha512_256.hash
    verified := Proof.Hmac.Stream.PPC64LE.Sha512_256.digest }]

end VG.Artifacts.Sha512.PPC64LE
