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
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTCode
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64

/-! # FFDH parameter generation calls each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Artifacts.Ffdh.AArch64
open VG.AArch64

def direct : List Artifact := [
  Spec.Ffdh.generationPrecomputeApi.artifact target {
    code := Impl.Ffdh.AArch64.Cached.Precompute.code Proof.Bignum.AArch64.Mont.productEight.mm
    verified := Proof.Ffdh.AArch64.Cached.precompute_verified _ },
  Spec.Ffdh.cachedGenerateKeyApi.artifact target {
    code := Impl.Ffdh.AArch64.Cached.Generate.code Proof.Bignum.AArch64.Mont.productEight.mm
    verified := Proof.Ffdh.AArch64.Cached.attempt_verified _ },
  Spec.Ffdh.cachedKeySearchApi.artifact target {
    stack := 64
    code := Proof.Ffdh.AArch64.Cached.cachedSearch
    verified := Proof.Ffdh.AArch64.Cached.cachedSearch_verified },
  Spec.Ffdh.checkPublicApi.artifact target {
    code := Impl.Ffdh.AArch64.Domain.CheckPublic.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.CheckPublic.cp_verified _ _ _ },
  Spec.Ffdh.checkDomainApi.artifact target {
    code := Impl.Ffdh.AArch64.VettedValidation.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.VettedValidation.verified _ _ _ },
  Spec.Ffdh.exchangeApi.artifact target {
    code := Impl.Ffdh.AArch64.Domain.Exchange.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.Exchange.ex_verified _ _ _ },
  Spec.Ffdh.checkPrivateApi.artifact target {
    code := Impl.Ffdh.AArch64.Domain.CheckPrivate.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.CheckPrivate.kp_verified _ _ _ },
  Spec.Ffdh.derivePublicApi.artifact target {
    code := Impl.Ffdh.AArch64.Domain.DerivePublic.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.Derive.dv_verified _ _ _ },
  Spec.Ffdh.parameterInitApi.artifact target {
    code := Impl.Ffdh.AArch64.Generation.init
    verified := Proof.Ffdh.AArch64.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact target {
    code := Impl.Ffdh.AArch64.KeyGeneration.init
    verified := Proof.Ffdh.AArch64.KeyGeneration.init_verified }]

end VG.Artifacts.Ffdh.AArch64

-- FFDH parameter generation calls each shared Miller–Rabin implementation
namespace VG.Artifacts.Ffdh.AArch64.MillerRabin

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact := [
  Spec.Ffdh.sievedParameterSearchApi.artifact AArch64.target {
    suffix := v.suffix
    stack := 32
    code := Proof.Ffdh.AArch64.Generation.searchCode v
    verified := Proof.Ffdh.AArch64.Generation.search_verified v
    features := v.features }]

end VG.Artifacts.Ffdh.AArch64.MillerRabin

namespace VG.Artifacts.Ffdh.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.AArch64.variants.flatMap fun v => MillerRabin.artifacts v)

end VG.Artifacts.Ffdh.AArch64
