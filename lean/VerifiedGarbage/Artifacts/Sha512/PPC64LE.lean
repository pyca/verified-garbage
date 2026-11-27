module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Sha512.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on PPC64LE -/

namespace VG.Artifacts.Sha512.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sha512.init384Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_384
    verified := Proof.Sha512.PPC64LE.init_scrubbed Spec.Sha512.H0_384 },
  Spec.Sha512.init512Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512
    verified := Proof.Sha512.PPC64LE.init_scrubbed Spec.Sha512.H0_512 },
  Spec.Sha512.init512_224Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512_224
    verified := Proof.Sha512.PPC64LE.init_scrubbed Spec.Sha512.H0_512_224 },
  Spec.Sha512.init512_256Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512_256
    verified := Proof.Sha512.PPC64LE.init_scrubbed Spec.Sha512.H0_512_256 },
  Spec.Sha512.updateApi.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.update
    verified := Proof.Sha512.PPC64LE.update_scrubbed },
  Spec.Sha512.finalizeApi.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.finalize
    verified := Proof.Sha512.PPC64LE.finalize_scrubbed },
  Spec.Sha512.finalize384Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.finalize384
    verified := Proof.Sha512.PPC64LE.finalize384_scrubbed },
  Spec.Sha512.finalize512_256Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.finalize512_256
    verified := Proof.Sha512.PPC64LE.finalize512_256_scrubbed },
  Spec.Sha512.finalize512_224Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.finalize512_224
    verified := Proof.Sha512.PPC64LE.finalize512_224_scrubbed },
  Spec.Sha512.digest384Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.digest384
    verified := Proof.Sha512.PPC64LE.digest384_scrubbed },
  Spec.Sha512.digest512Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.digest512
    verified := Proof.Sha512.PPC64LE.digest512_scrubbed },
  Spec.Sha512.digest512_224Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.digest512_224
    verified := Proof.Sha512.PPC64LE.digest512_224_scrubbed },
  Spec.Sha512.digest512_256Api.artifact PPC64LE.target {
    code := Impl.Sha512.PPC64LE.Fn.digest512_256
    verified := Proof.Sha512.PPC64LE.digest512_256_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sha512.PPC64LE
