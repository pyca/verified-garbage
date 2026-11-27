module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Finite-field Diffie–Hellman (SP 800-56A) on RISCV64 -/

namespace VG.Artifacts.Ffdh.RISCV64

def direct : List (Artifact RISCV64.target) := [
  Spec.Ffdh.parameterInitApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.parameterInit
    verified := Proof.Ffdh.RISCV64.Scrub.parameterInit_scrubbed
    publicOutOk := Proof.Ffdh.RISCV64.Scrub.parameterInit_public },
  Spec.Ffdh.keyInitApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.keyInit
    verified := Proof.Ffdh.RISCV64.Scrub.keyInit_scrubbed },
  Spec.Ffdh.checkPublicApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.checkPublic
    verified := Proof.Ffdh.RISCV64.Scrub.checkPublic_scrubbed },
  Spec.Ffdh.checkDomainApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.checkDomain
    verified := Proof.Ffdh.RISCV64.Scrub.checkDomain_scrubbed },
  Spec.Ffdh.exchangeApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.exchange
    verified := Proof.Ffdh.RISCV64.Scrub.exchange_scrubbed },
  Spec.Ffdh.derivePublicApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.derivePublic
    verified := Proof.Ffdh.RISCV64.Scrub.derivePublic_scrubbed },
  Spec.Ffdh.checkPrivateApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.checkPrivate
    verified := Proof.Ffdh.RISCV64.Scrub.checkPrivate_scrubbed },
  Spec.Ffdh.generationPrecomputeApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.precompute
    verified := Proof.Ffdh.RISCV64.Scrub.precompute_scrubbed },
  Spec.Ffdh.cachedKeySearchApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Fn.cachedKeySearch
    verified := Proof.Ffdh.RISCV64.Scrub.cachedKeySearch_scrubbed }]

public def artifacts : List (Artifact RISCV64.target) :=
  direct ++
  Proof.Variants.MillerRabin.RISCV64.variants.map fun (v : Proof.MillerRabin.RISCV64.RoundImpl) =>
    Spec.Ffdh.sievedParameterSearchApi.artifact RISCV64.target {
      suffix := v.suffix
      code := Impl.Ffdh.RISCV64.Fn.sievedParameterSearch v.suffix v.code
      verified := Proof.Ffdh.RISCV64.Scrub.sievedParameterSearch_scrubbed v
      publicOutOk := Proof.Ffdh.RISCV64.Scrub.sievedParameterSearch_public v }

spec_apis artifacts

end VG.Artifacts.Ffdh.RISCV64
