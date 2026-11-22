module

public import VerifiedGarbage.Proof.Ffdh.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Verified
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Verified
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckDomainInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPrivateInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeInstances

/-! # Finite-field Diffie–Hellman (SP 800-56A) on ARMv7 -/

@[expose] public section

-- Cached key generation and its native controller share one RSA arithmetic helper
namespace VG.Artifacts.Ffdh.Arm.Cached
open VG

def artifactsFor (v : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.generationPrecomputeApi.artifact VG.Arm.target {
    suffix := v.suffix
    code := Impl.Ffdh.Arm.Fn.generationPrecompute (Proof.Ffdh.Arm.combPrecomputeCalledCode v)
    verified := Proof.Ffdh.Arm.Fn.generationPrecompute v },
  Spec.Ffdh.cachedKeySearchApi.artifact VG.Arm.target {
    suffix := v.suffix
    code := Impl.Ffdh.Arm.Fn.cachedKeySearch
      (Proof.Ffdh.Arm.KeySearch.calledCode (Proof.Ffdh.Arm.CachedKeyGenerate.backend v))
    verified := Proof.Ffdh.Arm.Fn.cachedKeySearch v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ffdh.Arm.Cached

-- Deriving an imported scalar's public value inherits every shared RSA Montgomery backend
namespace VG.Artifacts.Ffdh.Arm.DerivePublic
open VG

def artifactsFor (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.derivePublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    code := Impl.Ffdh.Arm.Fn.derivePublic (Proof.Ffdh.Arm.SharedDerive.calledCode b)
    verified := Proof.Ffdh.Arm.Fn.derivePublic b }]

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ffdh.Arm.DerivePublic

-- Domain, public- and private-key validation inherit every shared RSA Montgomery backend
namespace VG.Artifacts.Ffdh.Arm.Domain.RsaMont
open VG

def artifacts (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.checkDomainApi.artifact VG.Arm.target {
    suffix := b.suffix
    code := Impl.Ffdh.Arm.Fn.checkDomain (Proof.Ffdh.Arm.SharedCheckDomain.calledCode b)
    verified := Proof.Ffdh.Arm.Fn.checkDomain b },
  Spec.Ffdh.checkPrivateApi.artifact VG.Arm.target {
    suffix := b.suffix
    code := Impl.Ffdh.Arm.Fn.checkPrivate (Proof.Ffdh.Arm.SharedCheckPrivate.calledCode b)
    verified := Proof.Ffdh.Arm.Fn.checkPrivate b },
  Spec.Ffdh.checkPublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    code := Impl.Ffdh.Arm.Fn.checkPublic (Proof.Ffdh.Arm.SharedCheckPublic.calledCode b)
    verified := Proof.Ffdh.Arm.Fn.checkPublic b }]

end VG.Artifacts.Ffdh.Arm.Domain.RsaMont

namespace VG.Artifacts.Ffdh.Arm.Domain

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => RsaMont.artifacts v

end VG.Artifacts.Ffdh.Arm.Domain

-- Shared-secret exponentiation inherits every shared RSA Montgomery backend
namespace VG.Artifacts.Ffdh.Arm.Exchange
open VG

def artifactsFor (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.exchangeApi.artifact VG.Arm.target {
    suffix := b.suffix
    code := Impl.Ffdh.Arm.Fn.exchange (Proof.Ffdh.Arm.SharedExchange.calledCode b)
    verified := Proof.Ffdh.Arm.Fn.exchange b }]

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ffdh.Arm.Exchange

namespace VG.Artifacts.Ffdh.Arm
open VG

def direct : List Artifact :=
  [
    Spec.Ffdh.keyInitApi.artifact VG.Arm.target {
      code := Impl.Ffdh.Arm.Fn.keyInit
      verified := Proof.Ffdh.Arm.Fn.keyInit },
    Spec.Ffdh.parameterInitApi.artifact VG.Arm.target {
      code := Impl.Ffdh.Arm.Fn.parameterInit
      verified := Proof.Ffdh.Arm.Fn.parameterInit }]

end VG.Artifacts.Ffdh.Arm

namespace VG.Artifacts.Ffdh.Arm

open VG

def artifacts : List Artifact :=
  Cached.artifacts ++
  DerivePublic.artifacts ++
  Domain.artifacts ++
  Exchange.artifacts ++
  direct ++
  (VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun (b : Proof.Bignum.Arm.MontBackend) =>
    (Proof.Ffdh.Arm.roundsFor b VG.Proof.Variants.MillerRabin.Arm.variants).flatMap
      fun (v : Proof.MillerRabin.Arm.RoundImpl) =>
    let c := Proof.Ffdh.Arm.parameterBackend v b
    [Spec.Ffdh.sievedParameterSearchApi.artifact VG.Arm.target {
      suffix := c.suffix
      code := Impl.Ffdh.Arm.Fn.sievedParameterSearch
        (Impl.Ffdh.Arm.ParameterSearch.code (.call c.candidateName c.candidate))
      verified := Proof.Ffdh.Arm.Fn.sievedParameterSearch v b }])

end VG.Artifacts.Ffdh.Arm
