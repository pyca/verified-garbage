module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Safety
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateVerified
public import VerifiedGarbage.Proof.Ffdh.X86.ExchangeVerified
public import VerifiedGarbage.Proof.Ffdh.X86.DeriveVerified
public import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
public import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreVerified
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.Shape
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # Finite-field Diffie–Hellman (SP 800-56A) on x86 -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86
open VG

def artifacts : List Artifact := [
  Spec.Ffdh.checkDomainApi.artifact X86.target {
    code := Impl.Ffdh.X86.VettedValidation.code
    verified := .unscrubbed Proof.Ffdh.X86.VettedValidation.verified
    spSafe := Proof.Ffdh.X86.VettedValidation.spSafe },
  Spec.Ffdh.checkPublicApi.artifact X86.target {
    code := Impl.Ffdh.X86.CheckPublic.code
    verified := .unscrubbed Proof.Ffdh.X86.CheckPublic.verified
    spSafe := Proof.Ffdh.X86.Shape.checkPublic_spSafe },
  Spec.Ffdh.checkPrivateApi.artifact X86.target {
    code := Impl.Ffdh.X86.CheckPrivate.code
    verified := .unscrubbed Proof.Ffdh.X86.CheckPrivate.verified
    spSafe := Proof.Ffdh.X86.Shape.checkPrivate_spSafe },
  Spec.Ffdh.exchangeApi.artifact X86.target {
    code := Impl.Ffdh.X86.Exchange.code
    verified := .unscrubbed Proof.Ffdh.X86.Exchange.verified
    spSafe := Proof.Ffdh.X86.Shape.exchange_spSafe },
  Spec.Ffdh.derivePublicApi.artifact X86.target {
    code := Impl.Ffdh.X86.DerivePublic.code
    verified := .unscrubbed Proof.Ffdh.X86.Derive.verified
    spSafe := Proof.Ffdh.X86.Shape.derivePublic_spSafe },
  Spec.Ffdh.keyInitApi.artifact X86.target {
    code := Impl.Ffdh.X86.KeyInit.code
    verified := .unscrubbed Proof.Ffdh.X86.KeyInit.verified },
  Spec.Ffdh.generationPrecomputeApi.artifact X86.target {
    code := Impl.Ffdh.X86.Cached.Precompute.code
    verified := .unscrubbed Proof.Ffdh.X86.Cached.Pre.pc_verified
    spSafe := Proof.Ffdh.X86.Shape.cachedPrecompute_spSafe },
  Spec.Ffdh.cachedKeySearchApi.artifact X86.target {
    code := Impl.Ffdh.X86.Cached.Search.code
    verified := .unscrubbed Proof.Ffdh.X86.Cached.Search.verified
    spSafe := Proof.Ffdh.X86.Shape.cachedSearch_spSafe },
  Spec.Ffdh.parameterInitApi.artifact X86.target {
    code := Impl.Ffdh.X86.ParamInit.code
    verified := .unscrubbed Proof.Ffdh.X86.ParamInit.verified },
  Spec.Ffdh.sievedParameterSearchApi.artifact X86.target {
    code := Impl.Ffdh.X86.ParamSearch.code
    verified := .unscrubbed Proof.Ffdh.X86.PSearch.verified
    spSafe := Proof.Ffdh.X86.Shape.paramSearch_spSafe }]

end VG.Artifacts.Ffdh.X86
