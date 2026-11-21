module

public import VerifiedGarbage.Proof.Sha512.X86.Scrub
public import VerifiedGarbage.Impl.Sha512.X86.Stream
public import VerifiedGarbage.Impl.Sha512.X86.Digest
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha512.X86.Lit

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha512.X86

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.init Spec.Sha512.H0_384
    verified := Proof.Sha512.X86.Scrub.init384_scrubbed },
  Spec.Sha512.init512Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.init Spec.Sha512.H0_512
    verified := Proof.Sha512.X86.Scrub.init512_scrubbed },
  Spec.Sha512.init512_224Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.init Spec.Sha512.H0_512_224
    verified := Proof.Sha512.X86.Scrub.init512_224_scrubbed },
  Spec.Sha512.init512_256Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.init Spec.Sha512.H0_512_256
    verified := Proof.Sha512.X86.Scrub.init512_256_scrubbed },
  Spec.Sha512.updateApi.artifact X86.target {
    code := Impl.Sha512.X86.Fn.update
    verified := Proof.Sha512.X86.Scrub.update_scrubbed },
  Spec.Sha512.finalizeApi.artifact X86.target {
    code := Impl.Sha512.X86.Fn.finalize
    verified := Proof.Sha512.X86.Scrub.finalize_scrubbed },
  Spec.Sha512.finalize384Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.finalizeDigest Impl.Sha512.X86.Stream.params384
    verified := Proof.Sha512.X86.Scrub.finalize384_scrubbed },
  Spec.Sha512.finalize512_256Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.finalizeDigest Impl.Sha512.X86.Stream.params512_256
    verified := Proof.Sha512.X86.Scrub.finalize512_256_scrubbed },
  Spec.Sha512.finalize512_224Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.finalizeDigest Impl.Sha512.X86.Stream.params512_224
    verified := Proof.Sha512.X86.Scrub.finalize512_224_scrubbed },
  Spec.Sha512.digest384Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.digest 48 "vg_sha384_init_core" Spec.Sha512.H0_384
    verified := Proof.Sha512.X86.Scrub.digest384_scrubbed },
  Spec.Sha512.digest512Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.digest 64 "vg_sha512_init_core" Spec.Sha512.H0_512
    verified := Proof.Sha512.X86.Scrub.digest512_scrubbed },
  Spec.Sha512.digest512_224Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.digest 28 "vg_sha512_224_init_core" Spec.Sha512.H0_512_224
    verified := Proof.Sha512.X86.Scrub.digest512_224_scrubbed },
  Spec.Sha512.digest512_256Api.artifact X86.target {
    code := Impl.Sha512.X86.Fn.digest 32 "vg_sha512_256_init_core" Spec.Sha512.H0_512_256
    verified := Proof.Sha512.X86.Scrub.digest512_256_scrubbed }]

end VG.Artifacts.Sha512.X86
