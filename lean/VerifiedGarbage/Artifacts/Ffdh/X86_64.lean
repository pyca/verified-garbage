module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Fn
public import VerifiedGarbage.Proof.Ffdh.X86_64.InitScrub
public import VerifiedGarbage.Proof.Ffdh.X86_64.RoundScrub
public import VerifiedGarbage.Proof.Ffdh.X86_64.DomainScrub
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64
public import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Finite-field Diffie–Hellman (SP 800-56A) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86_64
open VG.X86_64

def direct : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact target { code := Impl.Ffdh.X86_64.Fn.parameterInit, verified := .scrubbed Proof.Ffdh.X86_64.Scrub.parameterInit_scrubbed, spSafe := Proof.Ffdh.X86_64.Scrub.parameterInit_spSafe },
  Spec.Ffdh.keyInitApi.artifact target { code := Impl.Ffdh.X86_64.Fn.keyInit, verified := .scrubbed Proof.Ffdh.X86_64.Scrub.keyInit_scrubbed, spSafe := Proof.Ffdh.X86_64.Scrub.keyInit_spSafe }]
end VG.Artifacts.Ffdh.X86_64

-- Emit FFDH domain operations for every shared arithmetic backend and exponentiation
namespace VG.Artifacts.Ffdh.X86_64.MillerRabinFfdhExp

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) (e : Proof.Ffdh.X86_64.ExpImpl) : List Artifact := [
  Spec.Ffdh.checkPublicApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.checkPublic (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := .scrubbed (Proof.Ffdh.X86_64.DomainScrub.public_scrubbed v e)
    spSafe := Proof.Ffdh.X86_64.DomainScrub.public_spSafe v e },
  Spec.Ffdh.exchangeApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.exchange (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := .scrubbed (Proof.Ffdh.X86_64.DomainScrub.exchange_scrubbed v e)
    spSafe := Proof.Ffdh.X86_64.DomainScrub.exchange_spSafe v e },
  Spec.Ffdh.checkPrivateApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.checkPrivate (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := .scrubbed (Proof.Ffdh.X86_64.DomainScrub.private_scrubbed v e)
    spSafe := Proof.Ffdh.X86_64.DomainScrub.private_spSafe v e },
  Spec.Ffdh.derivePublicApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.derivePublic (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := .scrubbed (Proof.Ffdh.X86_64.DomainScrub.derive_scrubbed v e)
    spSafe := Proof.Ffdh.X86_64.DomainScrub.derive_spSafe v e },
  Spec.Ffdh.checkDomainApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    code := Impl.Ffdh.X86_64.Fn.checkDomain (Proof.Ffdh.X86_64.DomainScrub.level v e) v.mm (e.code v.mm)
    verified := .scrubbed (Proof.Ffdh.X86_64.DomainScrub.domain_scrubbed v e)
    spSafe := Proof.Ffdh.X86_64.DomainScrub.domain_spSafe v e }]

end VG.Artifacts.Ffdh.X86_64.MillerRabinFfdhExp

namespace VG.Artifacts.Ffdh.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.MillerRabin.X86_64.arithVariants.flatMap fun (v : Proof.MillerRabin.X86_64.RoundImpl) => [
    Spec.Ffdh.generationPrecomputeApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Ffdh.X86_64.Fn.generationPrecompute v.level v.mm
      verified := .scrubbed (Proof.Ffdh.X86_64.RoundScrub.precompute_scrubbed v)
      spSafe := Proof.Ffdh.X86_64.RoundScrub.precompute_spSafe v },
    Spec.Ffdh.cachedKeySearchApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Ffdh.X86_64.Fn.cachedKeySearch v.level ("vg_ffdh_generate_key_cached" ++ v.suffix) v.mm
      verified := .scrubbed (Proof.Ffdh.X86_64.RoundScrub.key_scrubbed v)
      spSafe := Proof.Ffdh.X86_64.RoundScrub.key_spSafe v }]) ++
  direct ++
  (VG.Proof.Variants.FfdhExp.X86_64.variants.flatMap fun v2 =>
    VG.Proof.Variants.MillerRabin.X86_64.arithVariants.flatMap fun v => MillerRabinFfdhExp.artifacts v v2) ++
  (VG.Proof.Variants.MillerRabin.X86_64.variants.flatMap fun (v : Proof.MillerRabin.X86_64.RoundImpl) => [
    Spec.Ffdh.sievedParameterSearchApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Ffdh.X86_64.Fn.sievedParameterSearch v.level v.mont.mm v.name v.code
      verified := .scrubbed (Proof.Ffdh.X86_64.RoundScrub.search_scrubbed v)
      spSafe := Proof.Ffdh.X86_64.RoundScrub.search_spSafe v }])

end VG.Artifacts.Ffdh.X86_64
