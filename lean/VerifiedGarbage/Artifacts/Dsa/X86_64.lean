module

public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.ParameterSearchInitScrub
public import VerifiedGarbage.Proof.Dsa.X86_64.BackendScrub
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchScrub
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.TCB.X86_64.Print

/-! # DSA (FIPS 186-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86_64

def direct : List Artifact := [
  Spec.Dsa.parameterInitApi.artifact X86_64.target { code := Impl.Dsa.X86_64.Fn.parameterInit, verified := .scrubbed Proof.Dsa.X86_64.ParameterSearchInit.init_scrubbed, spSafe := Proof.Dsa.X86_64.ParameterSearchInit.init_spSafe }]

end VG.Artifacts.Dsa.X86_64

namespace VG.Artifacts.Dsa.X86_64

open VG.Proof.Dsa.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.X86_64.variants.flatMap fun (v : Backend) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.randomSignPrevalidated v.level (prevalidatedSignerName v) v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.randomSign_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.randomSign_spSafe v },
    Spec.Dsa.validatePrivateKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.validatePrivateKey v.level v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.validatePrivate_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.validatePrivate_spSafe v },
    Spec.Dsa.validatePublicKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.validatePublicKey v.level v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.validatePublic_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.validatePublic_spSafe v },
    Spec.Dsa.verifyPrevalidatedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.verifyPrevalidated v.level v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.verify_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.verify_spSafe v },
    Spec.Dsa.generateKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.generateKey v.level (keygenCheckName v) (keygenDeriveName v) v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.generateKey_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.generateKey_spSafe v },
    Spec.Dsa.deriveKeyApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Dsa.X86_64.Fn.deriveKey v.level v.sq v.mul
      verified := .scrubbed (Proof.Dsa.X86_64.BackendScrub.deriveKey_scrubbed v)
      spSafe := Proof.Dsa.X86_64.BackendScrub.deriveKey_spSafe v }]) ++
  (Generation.RefillBackend.hashPairs.flatMap fun (p : Generation.RefillBackend.Hashes) =>
    VG.Proof.Variants.MillerRabin.X86_64.variants.map fun (v : Proof.MillerRabin.X86_64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact X86_64.target {
      suffix := qualifiedName "" [("sha1", p.sha1.suffix), ("sha256", p.sha256.suffix), ("mr", v.suffix)]
      code := Impl.Dsa.X86_64.Fn.parameterSearch (Proof.Dsa.X86_64.Generation.SearchScrub.level p v)
        (Generation.RefillBackend.name "sha1" p.sha1 v 128) (Generation.RefillBackend.name "sha256" p.sha256 v 256)
        (Generation.RefillBackend.name "sha256" p.sha256 v 384) (Generation.RefillBackend.body p.sha1 v 128)
        (Generation.RefillBackend.body p.sha256 v 256) (Generation.RefillBackend.body p.sha256 v 384)
      verified := .scrubbed (Proof.Dsa.X86_64.Generation.SearchScrub.search_scrubbed p v)
      spSafe := Proof.Dsa.X86_64.Generation.SearchScrub.search_spSafe p v })

end VG.Artifacts.Dsa.X86_64
