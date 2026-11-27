module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Scrub
import VerifiedGarbage.Impl.Ffdh.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Finite-field Diffie–Hellman (SP 800-56A) on PPC64LE -/

namespace VG.Artifacts.Ffdh.PPC64LE

def direct : List (Artifact PPC64LE.target) := [
  Spec.Ffdh.parameterInitApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Generation.init
    verified := Proof.Ffdh.PPC64LE.Scrub.parameterInit_scrubbed
    publicOutOk := Proof.Ffdh.PPC64LE.Scrub.parameterInit_public },
  Spec.Ffdh.keyInitApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.KeyGeneration.init
    verified := Proof.Ffdh.PPC64LE.Scrub.keyInit_scrubbed },
  Spec.Ffdh.checkPublicApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.checkPublic
    verified := Proof.Ffdh.PPC64LE.Scrub.checkPublic_scrubbed },
  Spec.Ffdh.checkDomainApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.checkDomain
    verified := Proof.Ffdh.PPC64LE.Scrub.checkDomain_scrubbed },
  Spec.Ffdh.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.exchange
    verified := Proof.Ffdh.PPC64LE.Scrub.exchange_scrubbed },
  Spec.Ffdh.derivePublicApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.derivePublic
    verified := Proof.Ffdh.PPC64LE.Scrub.derivePublic_scrubbed },
  Spec.Ffdh.checkPrivateApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.checkPrivate
    verified := Proof.Ffdh.PPC64LE.Scrub.checkPrivate_scrubbed },
  Spec.Ffdh.generationPrecomputeApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.precompute
    verified := Proof.Ffdh.PPC64LE.Scrub.precompute_scrubbed },
  Spec.Ffdh.cachedKeySearchApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.cachedKeySearch
    verified := Proof.Ffdh.PPC64LE.Scrub.cachedKeySearch_scrubbed }]

public def artifacts : List (Artifact PPC64LE.target) :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.map
    fun (vh : {v // v ∈ VG.Proof.Variants.MillerRabin.PPC64LE.variants}) =>
    Spec.Ffdh.sievedParameterSearchApi.artifact PPC64LE.target {
      suffix := vh.1.suffix
      code := Impl.Ffdh.PPC64LE.Fn.sievedParameterSearch vh.1.suffix vh.1.code
      verified := Proof.Ffdh.PPC64LE.Scrub.search_scrubbed vh.1 vh.2
      publicOutOk := Proof.Ffdh.PPC64LE.Scrub.search_public vh.1 vh.2 })

spec_apis artifacts

end VG.Artifacts.Ffdh.PPC64LE
