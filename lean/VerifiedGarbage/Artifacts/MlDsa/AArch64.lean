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
      verified := Proof.MlDsa.AArch64.Fn.keyGen44 v },
    Spec.MlDsa.keyGen65Api.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.keyGen v.callee Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.AArch64.Fn.keyGen65 v },
    Spec.MlDsa.keyGen87Api.artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.keyGen v.callee Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.AArch64.Fn.keyGen87 v }]

end VG.Artifacts.MlDsa.AArch64.KeyGen

-- ML-DSA (FIPS 204) public-key hash `tr = H(pk, 64)` on AArch64
namespace VG.Artifacts.MlDsa.AArch64.PkTr

def artifactsFor (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.pkTr44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.MlDsa.AArch64.Fn.pkTr v.callee Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.AArch64.Fn.pkTr44 v },
  Spec.MlDsa.pkTr65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.MlDsa.AArch64.Fn.pkTr v.callee Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.AArch64.Fn.pkTr65 v },
  Spec.MlDsa.pkTr87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.MlDsa.AArch64.Fn.pkTr v.callee Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.AArch64.Fn.pkTr87 v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap artifactsFor

end VG.Artifacts.MlDsa.AArch64.PkTr

-- ML-DSA (FIPS 204) signing on AArch64
namespace VG.Artifacts.MlDsa.AArch64.Sign
open VG VG.Spec.MlDsa

/-- Signing a message representative, with the key's bytes and with a prepared
key, for each parameter set. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) => [
    (signApi mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa44 "mldsa44" false
      verified := Proof.MlDsa.AArch64.Fn.sign44 v false },
    (preparedSignApi mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa44 "mldsa44" true
      verified := Proof.MlDsa.AArch64.Fn.sign44 v true },
    (signApi mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa65 "mldsa65" false
      verified := Proof.MlDsa.AArch64.Fn.sign65 v false },
    (preparedSignApi mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa65 "mldsa65" true
      verified := Proof.MlDsa.AArch64.Fn.sign65 v true },
    (signApi mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa87 "mldsa87" false
      verified := Proof.MlDsa.AArch64.Fn.sign87 v false },
    (preparedSignApi mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa87 "mldsa87" true
      verified := Proof.MlDsa.AArch64.Fn.sign87 v true }]

end VG.Artifacts.MlDsa.AArch64.Sign

-- ML-DSA (FIPS 204) on AArch64: signing messages
namespace VG.Artifacts.MlDsa.AArch64.SignMessage
open VG VG.Spec.MlDsa

/-- Signing a message, with the key's bytes and with a prepared key, for each
parameter set. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) => [
    (signMessageApi mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa44 "mldsa44" false
      verified := Proof.MlDsa.AArch64.Fn.signMessage44 v false },
    (preparedSignMessageApi mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa44 "mldsa44" true
      verified := Proof.MlDsa.AArch64.Fn.signMessage44 v true },
    (signMessageApi mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa65 "mldsa65" false
      verified := Proof.MlDsa.AArch64.Fn.signMessage65 v false },
    (preparedSignMessageApi mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa65 "mldsa65" true
      verified := Proof.MlDsa.AArch64.Fn.signMessage65 v true },
    (signMessageApi mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa87 "mldsa87" false
      verified := Proof.MlDsa.AArch64.Fn.signMessage87 v false },
    (preparedSignMessageApi mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa87 "mldsa87" true
      verified := Proof.MlDsa.AArch64.Fn.signMessage87 v true }]

end VG.Artifacts.MlDsa.AArch64.SignMessage

-- ML-DSA (FIPS 204) verification on AArch64
namespace VG.Artifacts.MlDsa.AArch64.Verify
open VG VG.Spec.MlDsa

/-- Verifying a signature of a message representative, with the key's bytes and
with a prepared key, for each parameter set. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) => [
    (verifyApi mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa44 "mldsa44" false
      verified := Proof.MlDsa.AArch64.Fn.verify44 v false },
    (preparedVerifyApi mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa44 "mldsa44" true
      verified := Proof.MlDsa.AArch64.Fn.verify44 v true },
    (verifyApi mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa65 "mldsa65" false
      verified := Proof.MlDsa.AArch64.Fn.verify65 v false },
    (preparedVerifyApi mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa65 "mldsa65" true
      verified := Proof.MlDsa.AArch64.Fn.verify65 v true },
    (verifyApi mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa87 "mldsa87" false
      verified := Proof.MlDsa.AArch64.Fn.verify87 v false },
    (preparedVerifyApi mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa87 "mldsa87" true
      verified := Proof.MlDsa.AArch64.Fn.verify87 v true }]

end VG.Artifacts.MlDsa.AArch64.Verify

-- ML-DSA (FIPS 204) on AArch64: verifying messages
namespace VG.Artifacts.MlDsa.AArch64.VerifyMessageCached
open VG VG.Spec.MlDsa

/-- Verifying a signature of a message, with the key's bytes and with a prepared
key, for each parameter set. -/
def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun (v : Proof.Sha3.AArch64.Permutation) => [
    (verifyMessageCachedApi mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa44 "mldsa44" false
      verified := Proof.MlDsa.AArch64.Fn.verifyMessage44 v false },
    (preparedVerifyMessageApi mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa44 "mldsa44" true
      verified := Proof.MlDsa.AArch64.Fn.verifyMessage44 v true },
    (verifyMessageCachedApi mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa65 "mldsa65" false
      verified := Proof.MlDsa.AArch64.Fn.verifyMessage65 v false },
    (preparedVerifyMessageApi mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa65 "mldsa65" true
      verified := Proof.MlDsa.AArch64.Fn.verifyMessage65 v true },
    (verifyMessageCachedApi mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa87 "mldsa87" false
      verified := Proof.MlDsa.AArch64.Fn.verifyMessage87 v false },
    (preparedVerifyMessageApi mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      suffix := v.callee.suffix
      code := Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa87 "mldsa87" true
      verified := Proof.MlDsa.AArch64.Fn.verifyMessage87 v true }]

end VG.Artifacts.MlDsa.AArch64.VerifyMessageCached

namespace VG.Artifacts.MlDsa.AArch64

def artifacts : List Artifact :=
  KeyGen.artifacts ++
  PkTr.artifacts ++
  [
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.preparePublic Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.AArch64.Fn.preparePublic44 },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.prepareSecret Spec.MlDsa.mlDsa44
      verified := Proof.MlDsa.AArch64.Fn.prepareSecret44 },
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.preparePublic Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.AArch64.Fn.preparePublic65 },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.prepareSecret Spec.MlDsa.mlDsa65
      verified := Proof.MlDsa.AArch64.Fn.prepareSecret65 },
    (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.preparePublic Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.AArch64.Fn.preparePublic87 },
    (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact AArch64.target {
      code := Impl.MlDsa.AArch64.Fn.prepareSecret Spec.MlDsa.mlDsa87
      verified := Proof.MlDsa.AArch64.Fn.prepareSecret87 }] ++
  Sign.artifacts ++
  SignMessage.artifacts ++
  Verify.artifacts ++
  VerifyMessageCached.artifacts

end VG.Artifacts.MlDsa.AArch64
