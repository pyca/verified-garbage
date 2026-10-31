module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Instances

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ffdh.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  Spec.Ffdh.generationPrecomputeApi.artifact target {
    consts := Impl.Ffdh.AArch64.Cached.Policy.tableConsts
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
    consts := Impl.Ffdh.AArch64.Cached.Policy.tableConsts
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
  Spec.Ffdh.generateKeyApi.artifact target {
    code := Impl.Ffdh.AArch64.Domain.GenerateKey.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.GenerateKey.gk_verified _ _ _ },
  Spec.Ffdh.parameterInitApi.artifact target {
    code := Impl.Ffdh.AArch64.Generation.init
    verified := Proof.Ffdh.AArch64.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact target {
    code := Impl.Ffdh.AArch64.KeyGeneration.init
    verified := Proof.Ffdh.AArch64.KeyGeneration.init_verified },
  Spec.Ffdh.keySearchApi.artifact target {
    stack := 48
    code := Proof.Ffdh.AArch64.KeyGeneration.keyCode
    verified := Proof.Ffdh.AArch64.KeyGeneration.key_verified_base }]

end VG.Artifacts.Ffdh.AArch64
