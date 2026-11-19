module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Instances
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Verified
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScrubSides
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTCode
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64

/-! # Finite-field Diffie–Hellman (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ffdh.AArch64
open VG.AArch64

def direct : List Artifact := [
  Spec.Ffdh.generationPrecomputeApi.artifact target Proof.Ffdh.AArch64.Scrub.precomputeReg,
  Spec.Ffdh.cachedKeySearchApi.artifact target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Proof.Ffdh.AArch64.Cached.cachedSearch
    verified := Proof.Ffdh.AArch64.Cached.cachedSearch_verified } Proof.Ffdh.AArch64.Scrub.clearMul
    (Proof.Ffdh.AArch64.Scrub.cachedKeySearchOk _) Proof.Ffdh.AArch64.Scrub.cachedKeySearchSide),
  Spec.Ffdh.checkPublicApi.artifact target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Ffdh.AArch64.Domain.CheckPublic.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.CheckPublic.cp_verified _ _ _ } Proof.Ffdh.AArch64.Scrub.clearWindow
    (Proof.Ffdh.AArch64.Scrub.checkPublicOk _) Proof.Ffdh.AArch64.Scrub.checkPublicSide),
  Spec.Ffdh.checkDomainApi.artifact target Proof.Ffdh.AArch64.Scrub.checkDomainReg,
  Spec.Ffdh.exchangeApi.artifact target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Ffdh.AArch64.Domain.Exchange.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.Exchange.ex_verified _ _ _ } Proof.Ffdh.AArch64.Scrub.clearWindow
    (Proof.Ffdh.AArch64.Scrub.exchangeOk _) Proof.Ffdh.AArch64.Scrub.exchangeSide),
  Spec.Ffdh.checkPrivateApi.artifact target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Ffdh.AArch64.Domain.CheckPrivate.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.CheckPrivate.kp_verified _ _ _ } Proof.Ffdh.AArch64.Scrub.clearWindow
    (Proof.Ffdh.AArch64.Scrub.checkPrivateOk _) Proof.Ffdh.AArch64.Scrub.checkPrivateSide),
  Spec.Ffdh.derivePublicApi.artifact target (VG.AArch64.ScrubAll.scrubAllOf {
    code := Impl.Ffdh.AArch64.Domain.DerivePublic.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.Derive.dv_verified _ _ _ } Proof.Ffdh.AArch64.Scrub.clearWindow
    (Proof.Ffdh.AArch64.Scrub.derivePublicOk _) Proof.Ffdh.AArch64.Scrub.derivePublicSide),
  Spec.Ffdh.parameterInitApi.artifact target {
    code := Impl.Ffdh.AArch64.Generation.init
    verified := Proof.Ffdh.AArch64.Generation.init_verified
    residue := some ⟨Proof.Ffdh.AArch64.Generation.init_noResidue _ _⟩ },
  Spec.Ffdh.keyInitApi.artifact target {
    code := Impl.Ffdh.AArch64.KeyGeneration.init
    verified := Proof.Ffdh.AArch64.KeyGeneration.init_verified
    residue := some ⟨Proof.Ffdh.AArch64.KeyGeneration.init_noResidue _ _⟩ }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.AArch64.variants.attach.flatMap
    fun (v : { v : Proof.MillerRabin.AArch64.RoundImpl // v ∈ _ }) => [
    Spec.Ffdh.sievedParameterSearchApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Proof.Ffdh.AArch64.Generation.searchCode v.1
      verified := Proof.Ffdh.AArch64.Generation.search_verified v.1 } Proof.Ffdh.AArch64.Scrub.clearMul
      (Proof.Ffdh.AArch64.Scrub.sievedParameterSearchOk _) (Proof.Ffdh.AArch64.Scrub.sievedParameterSearchSide v.1 v.2))])

end VG.Artifacts.Ffdh.AArch64
