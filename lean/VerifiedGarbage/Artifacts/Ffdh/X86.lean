module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.Ffdh.X86.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Finite-field Diffie–Hellman (SP 800-56A) on x86 -/

namespace VG.Artifacts.Ffdh.X86
open VG

public def artifacts : List (Artifact X86.target) := [
  Spec.Ffdh.checkDomainApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.checkDomain
    verified := Proof.Ffdh.X86.Scrub.checkDomain_scrubbed },
  Spec.Ffdh.checkPublicApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.checkPublic
    verified := Proof.Ffdh.X86.Scrub.checkPublic_scrubbed },
  Spec.Ffdh.checkPrivateApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.checkPrivate
    verified := Proof.Ffdh.X86.Scrub.checkPrivate_scrubbed },
  Spec.Ffdh.exchangeApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.exchange
    verified := Proof.Ffdh.X86.Scrub.exchange_scrubbed },
  Spec.Ffdh.derivePublicApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.derivePublic
    verified := Proof.Ffdh.X86.Scrub.derivePublic_scrubbed },
  Spec.Ffdh.keyInitApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.keyInit
    verified := Proof.Ffdh.X86.Scrub.keyInit_scrubbed },
  Spec.Ffdh.generationPrecomputeApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.generationPrecompute
    verified := Proof.Ffdh.X86.Scrub.generationPrecompute_scrubbed },
  Spec.Ffdh.cachedKeySearchApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.cachedKeySearch
    verified := Proof.Ffdh.X86.Scrub.cachedKeySearch_scrubbed },
  Spec.Ffdh.parameterInitApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.parameterInit
    verified := Proof.Ffdh.X86.Scrub.parameterInit_scrubbed
    publicOutOk := Proof.Ffdh.X86.Scrub.parameterInit_public },
  Spec.Ffdh.sievedParameterSearchApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.sievedParameterSearch
    verified := Proof.Ffdh.X86.Scrub.sievedParameterSearch_scrubbed
    publicOutOk := Proof.Ffdh.X86.Scrub.sievedParameterSearch_public }]

spec_apis artifacts

end VG.Artifacts.Ffdh.X86
