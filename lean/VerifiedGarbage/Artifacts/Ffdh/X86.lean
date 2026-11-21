module

public import VerifiedGarbage.Proof.Ffdh.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ffdh.X86.Fn
public import VerifiedGarbage.TCB.X86.Print

/-! # Finite-field Diffie–Hellman (SP 800-56A) on x86 -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86
open VG

def artifacts : List Artifact := [
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
    verified := Proof.Ffdh.X86.Scrub.parameterInit_scrubbed },
  Spec.Ffdh.sievedParameterSearchApi.artifact X86.target {
    code := Impl.Ffdh.X86.Fn.sievedParameterSearch
    verified := Proof.Ffdh.X86.Scrub.sievedParameterSearch_scrubbed }]

end VG.Artifacts.Ffdh.X86
