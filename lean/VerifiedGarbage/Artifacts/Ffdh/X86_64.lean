module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Impl.Ffdh.X86_64.Fn
import VerifiedGarbage.Impl.Ffdh.X86_64.ScalarPower
import VerifiedGarbage.Proof.Ffdh.X86_64.ScalarPower
import VerifiedGarbage.Proof.Ffdh.X86_64.InitScrub
import VerifiedGarbage.Proof.Ffdh.X86_64.RoundScrub
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainScrub
import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64
import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Finite-field Diffie–Hellman (SP 800-56A) on x86-64 -/

namespace VG.Artifacts.Ffdh.X86_64
open VG.X86_64

def direct : List (Artifact X86_64.target) := [
  Spec.Ffdh.parameterInitApi.artifact target { code := Impl.Ffdh.X86_64.Fn.parameterInit, verified := Proof.Ffdh.X86_64.Scrub.parameterInit_scrubbed, publicOutOk := Proof.Ffdh.X86_64.Scrub.parameterInit_public, spSafe := Proof.Ffdh.X86_64.Scrub.parameterInit_spSafe },
  Spec.Ffdh.keyInitApi.artifact target { code := Impl.Ffdh.X86_64.Fn.keyInit, verified := Proof.Ffdh.X86_64.Scrub.keyInit_scrubbed, spSafe := Proof.Ffdh.X86_64.Scrub.keyInit_spSafe }]
end VG.Artifacts.Ffdh.X86_64

-- Emit FFDH domain operations for every shared arithmetic backend and exponentiation
namespace VG.Artifacts.Ffdh.X86_64.MillerRabinFfdhExp

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) (e : Proof.Ffdh.X86_64.ExpImpl) :
    List (Artifact X86_64.target) := [
  Spec.Ffdh.checkPublicApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.checkPublic (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := Proof.Ffdh.X86_64.DomainScrub.public_scrubbed v e
    spSafe := Proof.Ffdh.X86_64.DomainScrub.public_spSafe v e },
  Spec.Ffdh.exchangeApi.artifact X86_64.target (
    if v.suffix.isEmpty && e.suffix.isEmpty then {
      code := Impl.Ffdh.X86_64.Fn.exchangeScalar
      verified := Proof.Ffdh.X86_64.ScalarPower.exchange_scrubbed }
    else {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.exchange (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := Proof.Ffdh.X86_64.DomainScrub.exchange_scrubbed v e
    spSafe := Proof.Ffdh.X86_64.DomainScrub.exchange_spSafe v e }),
  Spec.Ffdh.checkPrivateApi.artifact X86_64.target (
    if v.suffix.isEmpty && e.suffix.isEmpty then {
      code := Impl.Ffdh.X86_64.Fn.checkPrivateScalar
      verified := Proof.Ffdh.X86_64.ScalarPower.private_scrubbed }
    else {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.checkPrivate (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := Proof.Ffdh.X86_64.DomainScrub.private_scrubbed v e
    spSafe := Proof.Ffdh.X86_64.DomainScrub.private_spSafe v e }),
  Spec.Ffdh.derivePublicApi.artifact X86_64.target (
    if v.suffix.isEmpty && e.suffix.isEmpty then {
      code := Impl.Ffdh.X86_64.Fn.derivePublicScalar
      verified := Proof.Ffdh.X86_64.ScalarPower.derive_scrubbed }
    else {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.derivePublic (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := Proof.Ffdh.X86_64.DomainScrub.derive_scrubbed v e
    spSafe := Proof.Ffdh.X86_64.DomainScrub.derive_spSafe v e }),
  Spec.Ffdh.checkDomainApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.checkDomain (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := Proof.Ffdh.X86_64.DomainScrub.domain_scrubbed v e
    spSafe := Proof.Ffdh.X86_64.DomainScrub.domain_spSafe v e }]

end VG.Artifacts.Ffdh.X86_64.MillerRabinFfdhExp

namespace VG.Artifacts.Ffdh.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  (VG.Proof.Variants.MillerRabin.X86_64.arithVariants.flatMap fun (v : Proof.MillerRabin.X86_64.RoundImpl) => [
    Spec.Ffdh.generationPrecomputeApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Ffdh.X86_64.Fn.generationPrecompute v.level v.mm
      verified := Proof.Ffdh.X86_64.RoundScrub.precompute_scrubbed v
      spSafe := Proof.Ffdh.X86_64.RoundScrub.precompute_spSafe v },
    Spec.Ffdh.cachedKeySearchApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Ffdh.X86_64.Fn.cachedKeySearch v.level ("vg_ffdh_generate_key_cached" ++ v.suffix) v.mm
      verified := Proof.Ffdh.X86_64.RoundScrub.key_scrubbed v
      spSafe := Proof.Ffdh.X86_64.RoundScrub.key_spSafe v }]) ++
  direct ++
  (VG.Proof.Variants.FfdhExp.X86_64.variants.flatMap fun v2 =>
    VG.Proof.Variants.MillerRabin.X86_64.arithVariants.flatMap fun v => MillerRabinFfdhExp.artifacts v v2) ++
  (VG.Proof.Variants.MillerRabin.X86_64.variants.flatMap fun (v : Proof.MillerRabin.X86_64.RoundImpl) => [
    Spec.Ffdh.sievedParameterSearchApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Ffdh.X86_64.Fn.sievedParameterSearch v.level v.mont.mm ("vg_ffdh_prepare_modulus" ++ v.arithSuffix) v.name v.code
      verified := Proof.Ffdh.X86_64.RoundScrub.search_scrubbed v
      publicOutOk := Proof.Ffdh.X86_64.RoundScrub.search_public v
      spSafe := Proof.Ffdh.X86_64.RoundScrub.search_spSafe v }])

spec_apis artifacts

end VG.Artifacts.Ffdh.X86_64
