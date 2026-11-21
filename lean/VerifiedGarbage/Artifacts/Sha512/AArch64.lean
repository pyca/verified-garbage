module

public import VerifiedGarbage.Proof.Sha512.AArch64.Shared
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.AArch64.Sha3.Compress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512
public import VerifiedGarbage.Proof.Variants.Sha512Compress.AArch64

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha512.AArch64

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact AArch64.target {
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_384
    verified := Proof.Sha512.AArch64.Stream.init384_scrubbed },
  Spec.Sha512.init512Api.artifact AArch64.target {
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512
    verified := Proof.Sha512.AArch64.Stream.init512_scrubbed },
  Spec.Sha512.init512_224Api.artifact AArch64.target {
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_224
    verified := Proof.Sha512.AArch64.Stream.init512_224_scrubbed },
  Spec.Sha512.init512_256Api.artifact AArch64.target {
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_256
    verified := Proof.Sha512.AArch64.Stream.init512_256_scrubbed }] ++
  (VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun (v : Proof.Sha512.AArch64.Compress) => [
    Spec.Sha512.finalize384Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.finalize384 v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.finalize384_scrubbed v },
    Spec.Sha512.digest384Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.digest384 v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.digest384_scrubbed v }]) ++
  (VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun (v : Proof.Sha512.AArch64.Compress) => [
    Spec.Sha512.updateApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.update v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.update_scrubbed v },
    Spec.Sha512.finalizeApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.finalize v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.finalize_scrubbed v },
    Spec.Sha512.digest512Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.digest512 v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.digest512_scrubbed v }]) ++
  (VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun (v : Proof.Sha512.AArch64.Compress) => [
    Spec.Sha512.finalize512_224Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.finalize512_224 v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.finalize512_224_scrubbed v },
    Spec.Sha512.digest512_224Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.digest512_224 v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.digest512_224_scrubbed v }]) ++
  (VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun (v : Proof.Sha512.AArch64.Compress) => [
    Spec.Sha512.finalize512_256Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.finalize512_256 v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.finalize512_256_scrubbed v },
    Spec.Sha512.digest512_256Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha512.AArch64.Stream.Fn.digest512_256 v.suffix v.code
      verified := Proof.Pbkdf2.Md.AArch64.Sha512.digest512_256_scrubbed v }])

end VG.Artifacts.Sha512.AArch64
