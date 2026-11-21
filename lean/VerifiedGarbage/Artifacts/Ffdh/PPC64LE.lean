module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Scrub
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # Finite-field Diffie–Hellman (SP 800-56A) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ffdh.PPC64LE

def direct : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Generation.init
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.parameterInit_scrubbed },
  Spec.Ffdh.keyInitApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.KeyGeneration.init
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.keyInit_scrubbed },
  Spec.Ffdh.checkPublicApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.checkPublic
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.checkPublic_scrubbed },
  Spec.Ffdh.checkDomainApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.checkDomain
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.checkDomain_scrubbed },
  Spec.Ffdh.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.exchange
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.exchange_scrubbed },
  Spec.Ffdh.derivePublicApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.derivePublic
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.derivePublic_scrubbed },
  Spec.Ffdh.checkPrivateApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.checkPrivate
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.checkPrivate_scrubbed },
  Spec.Ffdh.generationPrecomputeApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.precompute
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.precompute_scrubbed },
  Spec.Ffdh.cachedKeySearchApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Fn.cachedKeySearch
    verified := .scrubbed Proof.Ffdh.PPC64LE.Scrub.cachedKeySearch_scrubbed }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.map fun ⟨v, hv⟩ =>
    Spec.Ffdh.sievedParameterSearchApi.artifact PPC64LE.target {
      suffix := v.suffix
      code := Impl.Ffdh.PPC64LE.Fn.sievedParameterSearch v.suffix v.code
      verified := .scrubbed (Proof.Ffdh.PPC64LE.Scrub.search_scrubbed v hv) })

end VG.Artifacts.Ffdh.PPC64LE
