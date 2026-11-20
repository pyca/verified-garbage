module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ML-DSA (FIPS 204) on AArch64 -/

@[expose] public section

-- ML-DSA (FIPS 204) key generation on AArch64
namespace VG.Artifacts.MlDsa.AArch64.KeyGen

/-- Key generation over the permutation `v`: hoisted matrix seeds, grouped
secret sampling with the four-way samplers of `v`, and positive transform
arithmetic, which needs no CPU feature. Where the paired-state kernels may
use the SHA3 instructions (`pairedSha3`), the matrix entries left after the
groups of four are sampled as a pair; otherwise one at a time. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) => [
    Spec.MlDsa.keyGen44Api.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.keyGen v.callee Spec.MlDsa.mlDsa44
      verified := .scrubbed (Proof.MlDsa.AArch64.Fn.keyGen44 v) },
    Spec.MlDsa.keyGen65Api.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.keyGen v.callee Spec.MlDsa.mlDsa65
      verified := .scrubbed (Proof.MlDsa.AArch64.Fn.keyGen65 v) },
    Spec.MlDsa.keyGen87Api.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.keyGen v.callee Spec.MlDsa.mlDsa87
      verified := .scrubbed (Proof.MlDsa.AArch64.Fn.keyGen87 v) }]

end VG.Artifacts.MlDsa.AArch64.KeyGen

-- ML-DSA (FIPS 204) public-key hash `tr = H(pk, 64)` on AArch64
namespace VG.Artifacts.MlDsa.AArch64.PkTr

def artifactsFor (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.pkTr44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.MlDsa.AArch64.Fn.pkTr v.callee Spec.MlDsa.mlDsa44
    verified := .scrubbed (Proof.MlDsa.AArch64.Fn.pkTr44 v) },
  Spec.MlDsa.pkTr65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.MlDsa.AArch64.Fn.pkTr v.callee Spec.MlDsa.mlDsa65
    verified := .scrubbed (Proof.MlDsa.AArch64.Fn.pkTr65 v) },
  Spec.MlDsa.pkTr87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.MlDsa.AArch64.Fn.pkTr v.callee Spec.MlDsa.mlDsa87
    verified := .scrubbed (Proof.MlDsa.AArch64.Fn.pkTr87 v) }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap artifactsFor

end VG.Artifacts.MlDsa.AArch64.PkTr

-- ML-DSA (FIPS 204) signing on AArch64
namespace VG.Artifacts.MlDsa.AArch64.Sign
open VG VG.Spec.MlDsa

/-- Signing a message representative, with the key's bytes and with a prepared
key, for each parameter set. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) =>
    Proof.MlDsa.AArch64.Scrub.sets.flatMap fun (s : Proof.MlDsa.AArch64.Scrub.ParamSet) => [
      (signApi s.p s.module s.label).artifact AArch64.target {
        suffix := v.callee.suffix
        code := Impl.MlDsa.AArch64.Fn.sign v.callee s.p s.module false
        verified := .scrubbed (Proof.MlDsa.AArch64.Fn.sign v s false) },
      (preparedSignApi s.p s.module s.label).artifact AArch64.target {
        suffix := v.callee.suffix
        code := Impl.MlDsa.AArch64.Fn.sign v.callee s.p s.module true
        verified := .scrubbed (Proof.MlDsa.AArch64.Fn.sign v s true) }]

end VG.Artifacts.MlDsa.AArch64.Sign

-- ML-DSA (FIPS 204) on AArch64: signing messages
namespace VG.Artifacts.MlDsa.AArch64.SignMessage
open VG VG.Spec.MlDsa

/-- Signing a message, with the key's bytes and with a prepared key, for each
parameter set. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) =>
    Proof.MlDsa.AArch64.Scrub.sets.flatMap fun (s : Proof.MlDsa.AArch64.Scrub.ParamSet) => [
      (signMessageApi s.p s.module s.label).artifact AArch64.target {
        suffix := v.callee.suffix
        code := Impl.MlDsa.AArch64.Fn.signMessage v.callee s.p s.module false
        verified := .scrubbed (Proof.MlDsa.AArch64.Fn.signMessage v s false) },
      (preparedSignMessageApi s.p s.module s.label).artifact AArch64.target {
        suffix := v.callee.suffix
        code := Impl.MlDsa.AArch64.Fn.signMessage v.callee s.p s.module true
        verified := .scrubbed (Proof.MlDsa.AArch64.Fn.signMessage v s true) }]

end VG.Artifacts.MlDsa.AArch64.SignMessage

-- ML-DSA (FIPS 204) verification on AArch64
namespace VG.Artifacts.MlDsa.AArch64.Verify
open VG VG.Spec.MlDsa

/-- Verifying a signature of a message representative, with the key's bytes and
with a prepared key, for each parameter set. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) =>
    Proof.MlDsa.AArch64.Scrub.sets.flatMap fun (s : Proof.MlDsa.AArch64.Scrub.ParamSet) => [
      (verifyApi s.p s.module s.label).artifact AArch64.target {
        suffix := v.callee.suffix
        code := Impl.MlDsa.AArch64.Fn.verify v.callee s.p s.module false
        verified := .scrubbed (Proof.MlDsa.AArch64.Fn.verify v s false) },
      (preparedVerifyApi s.p s.module s.label).artifact AArch64.target {
        suffix := v.callee.suffix
        code := Impl.MlDsa.AArch64.Fn.verify v.callee s.p s.module true
        verified := .scrubbed (Proof.MlDsa.AArch64.Fn.verify v s true) }]

end VG.Artifacts.MlDsa.AArch64.Verify

-- ML-DSA (FIPS 204) on AArch64: verifying messages
namespace VG.Artifacts.MlDsa.AArch64.VerifyMessageCached
open VG VG.Spec.MlDsa

/-- Verifying a signature of a message, with the key's bytes and with a prepared
key, for each parameter set. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) =>
    Proof.MlDsa.AArch64.Scrub.sets.flatMap fun (s : Proof.MlDsa.AArch64.Scrub.ParamSet) => [
      (verifyMessageCachedApi s.p s.module s.label).artifact AArch64.target {
        suffix := v.callee.suffix
        code := Impl.MlDsa.AArch64.Fn.verifyMessage v.callee s.p s.module false
        verified := .scrubbed (Proof.MlDsa.AArch64.Fn.verifyMessage v s false) },
      (preparedVerifyMessageApi s.p s.module s.label).artifact AArch64.target {
        suffix := v.callee.suffix
        code := Impl.MlDsa.AArch64.Fn.verifyMessage v.callee s.p s.module true
        verified := .scrubbed (Proof.MlDsa.AArch64.Fn.verifyMessage v s true) }]

end VG.Artifacts.MlDsa.AArch64.VerifyMessageCached

namespace VG.Artifacts.MlDsa.AArch64

def artifacts : List Artifact :=
  KeyGen.artifacts ++
  PkTr.artifacts ++
  [
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.preparePublic Spec.MlDsa.mlDsa44
      verified := .scrubbed Proof.MlDsa.AArch64.Fn.preparePublic44 },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.prepareSecret Spec.MlDsa.mlDsa44
      verified := .scrubbed Proof.MlDsa.AArch64.Fn.prepareSecret44 },
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.preparePublic Spec.MlDsa.mlDsa65
      verified := .scrubbed Proof.MlDsa.AArch64.Fn.preparePublic65 },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.prepareSecret Spec.MlDsa.mlDsa65
      verified := .scrubbed Proof.MlDsa.AArch64.Fn.prepareSecret65 },
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.preparePublic Spec.MlDsa.mlDsa87
      verified := .scrubbed Proof.MlDsa.AArch64.Fn.preparePublic87 },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.prepareSecret Spec.MlDsa.mlDsa87
      verified := .scrubbed Proof.MlDsa.AArch64.Fn.prepareSecret87 }] ++
  Sign.artifacts ++
  SignMessage.artifacts ++
  Verify.artifacts ++
  VerifyMessageCached.artifacts

end VG.Artifacts.MlDsa.AArch64
