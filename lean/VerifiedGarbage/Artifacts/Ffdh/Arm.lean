module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyInitVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInitVerified
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
public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Variants.Ffdh.Arm
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeInstances

/-! # Finite-field Diffie–Hellman (SP 800-56A) on ARMv7 -/

@[expose] public section

-- Cached key generation and its native controller share one RSA arithmetic helper
namespace VG.Artifacts.Ffdh.Arm.Cached
open VG

def artifactsFor (v : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.generationPrecomputeApi.artifact VG.Arm.target {
    suffix := v.suffix
    stack := 176
    code := Proof.Ffdh.Arm.combPrecomputeCalledCode v
    verified := Proof.Ffdh.Arm.combPrecomputeCalled_verified v },
  Spec.Ffdh.cachedGenerateKeyApi.artifact VG.Arm.target {
    suffix := v.suffix
    stack := 176
    code := (Proof.Ffdh.Arm.CachedKeyGenerate.backend v).generateKey
    verified := (Proof.Ffdh.Arm.CachedKeyGenerate.backend v).generateKey_verified },
  Spec.Ffdh.cachedKeySearchApi.artifact VG.Arm.target {
    suffix := v.suffix
    stack := Proof.Ffdh.Arm.KeySearch.stackUse .cached
    code := Proof.Ffdh.Arm.KeySearch.calledCode
      (Proof.Ffdh.Arm.CachedKeyGenerate.backend v)
    verified := Proof.Ffdh.Arm.KeySearch.verified (Proof.Ffdh.Arm.CachedKeyGenerate.backend v) }]

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ffdh.Arm.Cached

-- Deriving an imported scalar's public value inherits every shared RSA Montgomery backend
namespace VG.Artifacts.Ffdh.Arm.DerivePublic
open VG

def artifactsFor (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.derivePublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    stack := 176
    code := Proof.Ffdh.Arm.SharedDerive.calledCode b
    verified := Proof.Ffdh.Arm.SharedDerive.called_verified b }]

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ffdh.Arm.DerivePublic

-- Emit every native ARMv7 FFDH backend
namespace VG.Artifacts.Ffdh.Arm.Domain.Ffdh
open VG

def artifacts (v : Proof.Ffdh.Arm.Backend) : List Artifact :=
  [Spec.Ffdh.checkDomainApi.artifact VG.Arm.target {
    suffix := v.suffix
    stack := 128
    code := v.checkDomain
    verified := v.checkDomain_verified },
  Spec.Ffdh.checkPrivateApi.artifact VG.Arm.target {
    suffix := v.suffix
    stack := 128
    code := v.checkPrivate
    verified := v.checkPrivate_verified }]

end VG.Artifacts.Ffdh.Arm.Domain.Ffdh

-- Public-key validation inherits every shared RSA Montgomery backend
namespace VG.Artifacts.Ffdh.Arm.Domain.RsaMont
open VG

def artifacts (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.checkPublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    stack := 176
    code := Proof.Ffdh.Arm.SharedCheckPublic.calledCode b
    verified := Proof.Ffdh.Arm.SharedCheckPublic.called_verified b }]

end VG.Artifacts.Ffdh.Arm.Domain.RsaMont

namespace VG.Artifacts.Ffdh.Arm.Domain

def artifacts : List Artifact :=
  (VG.Proof.Variants.Ffdh.Arm.variants.flatMap fun v => Ffdh.artifacts v) ++
  (VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => RsaMont.artifacts v)

end VG.Artifacts.Ffdh.Arm.Domain

-- Shared-secret exponentiation inherits every shared RSA Montgomery backend
namespace VG.Artifacts.Ffdh.Arm.Exchange
open VG

def artifactsFor (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.exchangeApi.artifact VG.Arm.target {
    suffix := b.suffix
    stack := 176
    code := Proof.Ffdh.Arm.SharedExchange.calledCode b
    verified := Proof.Ffdh.Arm.SharedExchange.called_verified b }]

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ffdh.Arm.Exchange

namespace VG.Artifacts.Ffdh.Arm
open VG

def direct : List Artifact :=
  [
    Spec.Ffdh.keyInitApi.artifact VG.Arm.target {
      code := Impl.Ffdh.Arm.KeyGeneration.init
      verified := Proof.Ffdh.Arm.keyInit_verified },
    Spec.Ffdh.parameterInitApi.artifact VG.Arm.target {
      code := Impl.Ffdh.Arm.Generation.init
      verified := Proof.Ffdh.Arm.parameterInit_verified }]

end VG.Artifacts.Ffdh.Arm

namespace VG.Artifacts.Ffdh.Arm

open VG

def artifacts : List Artifact :=
  Cached.artifacts ++
  DerivePublic.artifacts ++
  Domain.artifacts ++
  Exchange.artifacts ++
  direct ++
  (VG.Proof.Variants.MillerRabin.Arm.variants.flatMap fun (v : Proof.MillerRabin.Arm.RoundImpl) =>
    let b := Proof.Ffdh.Arm.parameterBackend v
    [Spec.Ffdh.sievedParameterSearchApi.artifact VG.Arm.target {
      suffix := b.suffix
      stack := 232
      code := Impl.Ffdh.Arm.ParameterSearch.code (.call b.candidateName b.candidate)
      verified := Proof.Ffdh.Arm.ParameterSearch.verified b }])

end VG.Artifacts.Ffdh.Arm
