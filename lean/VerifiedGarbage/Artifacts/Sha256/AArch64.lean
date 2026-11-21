module

public import VerifiedGarbage.Proof.Sha256.AArch64.Shared
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Compress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512
public import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64
public import VerifiedGarbage.Proof.Sha256.AArch64.Residue

/-! # SHA-256 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha256.AArch64

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact AArch64.target {
    code := Impl.Sha256.AArch64.Stream.init224
    verified := .scrubbed Proof.Sha256.AArch64.Residue.init224_scrubbed },
  Spec.Sha256.initApi.artifact AArch64.target {
    code := Impl.Sha256.AArch64.Stream.init
    verified := .scrubbed Proof.Sha256.AArch64.Residue.init_scrubbed }] ++
  (VG.Proof.Variants.Sha256Compress.AArch64.variants.flatMap fun (v : Proof.Sha256.AArch64.Compress) => [
    Spec.Sha256.finalize224Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha256.AArch64.Stream.Fn.finalize224 v.name v.code
      verified := .scrubbed (Proof.Pbkdf2.Md.AArch64.Sha224.finalize224_scrubbed v) },
    Spec.Sha256.digest224Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha256.AArch64.Stream.Fn.digest224 v.name v.code
      verified := .scrubbed (Proof.Pbkdf2.Md.AArch64.Sha224.digest224_scrubbed v) }]) ++
  (VG.Proof.Variants.Sha256Compress.AArch64.variants.flatMap fun (v : Proof.Sha256.AArch64.Compress) => [
    Spec.Sha256.updateApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha256.AArch64.Stream.Fn.update v.name v.code
      verified := .scrubbed (Proof.Pbkdf2.Md.AArch64.Sha256.update_scrubbed v) },
    Spec.Sha256.finalizeApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha256.AArch64.Stream.Fn.finalize v.name v.code
      verified := .scrubbed (Proof.Pbkdf2.Md.AArch64.Sha256.finalize_scrubbed v) },
    Spec.Sha256.digest256Api.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sha256.AArch64.Stream.Fn.digest256 v.name v.code
      verified := .scrubbed (Proof.Pbkdf2.Md.AArch64.Sha256.digest256_scrubbed v) }])

end VG.Artifacts.Sha256.AArch64
