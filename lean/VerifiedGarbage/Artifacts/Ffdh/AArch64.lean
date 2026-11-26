module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.AArch64.ScrubSides
import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Finite-field Diffie–Hellman (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.Ffdh.AArch64
open VG.AArch64

def direct : List (Artifact AArch64.target) := [
  Spec.Ffdh.generationPrecomputeApi.artifact target {
    code := Impl.Ffdh.AArch64.Fn.precompute
    verified := Proof.Ffdh.AArch64.Scrub.precompute_scrubbed },
  Spec.Ffdh.cachedKeySearchApi.artifact target {
    code := Impl.Ffdh.AArch64.Fn.cachedKeySearch
    verified := Proof.Ffdh.AArch64.Scrub.cachedKeySearch_scrubbed },
  Spec.Ffdh.checkPublicApi.artifact target {
    code := Impl.Ffdh.AArch64.Fn.checkPublic
    verified := Proof.Ffdh.AArch64.Scrub.checkPublic_scrubbed },
  Spec.Ffdh.checkDomainApi.artifact target {
    code := Impl.Ffdh.AArch64.Fn.checkDomain
    verified := Proof.Ffdh.AArch64.Scrub.checkDomain_scrubbed },
  Spec.Ffdh.exchangeApi.artifact target {
    code := Impl.Ffdh.AArch64.Fn.exchange
    verified := Proof.Ffdh.AArch64.Scrub.exchange_scrubbed },
  Spec.Ffdh.checkPrivateApi.artifact target {
    code := Impl.Ffdh.AArch64.Fn.checkPrivate
    verified := Proof.Ffdh.AArch64.Scrub.checkPrivate_scrubbed },
  Spec.Ffdh.derivePublicApi.artifact target {
    code := Impl.Ffdh.AArch64.Fn.derivePublic
    verified := Proof.Ffdh.AArch64.Scrub.derivePublic_scrubbed },
  Spec.Ffdh.parameterInitApi.artifact target {
    code := Impl.Ffdh.AArch64.Generation.init
    verified := Proof.Ffdh.AArch64.Scrub.parameterInit_scrubbed
    publicOutOk := Proof.Ffdh.AArch64.Scrub.parameterInit_public },
  Spec.Ffdh.keyInitApi.artifact target {
    code := Impl.Ffdh.AArch64.KeyGeneration.init
    verified := Proof.Ffdh.AArch64.Scrub.keyInit_scrubbed }]

public def artifacts : List (Artifact AArch64.target) :=
  direct ++
  (VG.Proof.Variants.MillerRabin.AArch64.variants.flatMap fun (v : Proof.MillerRabin.AArch64.RoundImpl) => [
    Spec.Ffdh.sievedParameterSearchApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Ffdh.AArch64.Fn.parameterSearch v.suffix v.mont.mm v.roundMont.mm
      verified := Proof.Ffdh.AArch64.Generation.parameterSearch_scrubbed v
      publicOutOk := Proof.Ffdh.AArch64.Generation.parameterSearch_public v }])

spec_apis artifacts

end VG.Artifacts.Ffdh.AArch64
