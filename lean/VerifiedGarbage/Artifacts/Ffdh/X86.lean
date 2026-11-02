module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Safety
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateVerified
public import VerifiedGarbage.Proof.Ffdh.X86.ExchangeVerified
public import VerifiedGarbage.Proof.Ffdh.X86.DeriveVerified
public import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenVerified
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.Shape
public import VerifiedGarbage.Proof.Framework.Registration

/-! # FFDH's domain and key checks, exchange, key generation and parameter candidates on baseline i686 -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86
open VG

def artifacts : List Artifact := [
  Spec.Ffdh.checkDomainApi.artifact X86.target {
    consts := Impl.Ffdh.X86.VettedValidation.tableConsts
    code := Impl.Ffdh.X86.VettedValidation.code
    verified := Proof.Ffdh.X86.VettedValidation.verified
    spSafe := Proof.Ffdh.X86.VettedValidation.spSafe
    stack := 172 },
  Spec.Ffdh.checkPublicApi.artifact X86.target {
    code := Impl.Ffdh.X86.CheckPublic.code
    verified := Proof.Ffdh.X86.CheckPublic.verified
    spSafe := Proof.Ffdh.X86.Shape.checkPublic_spSafe
    stack := 172 },
  Spec.Ffdh.checkPrivateApi.artifact X86.target {
    code := Impl.Ffdh.X86.CheckPrivate.code
    verified := Proof.Ffdh.X86.CheckPrivate.verified
    spSafe := Proof.Ffdh.X86.Shape.checkPrivate_spSafe
    stack := 172 },
  Spec.Ffdh.exchangeApi.artifact X86.target {
    code := Impl.Ffdh.X86.Exchange.code
    verified := Proof.Ffdh.X86.Exchange.verified
    spSafe := Proof.Ffdh.X86.Shape.exchange_spSafe
    stack := 172 },
  Spec.Ffdh.derivePublicApi.artifact X86.target {
    code := Impl.Ffdh.X86.DerivePublic.code
    verified := Proof.Ffdh.X86.Derive.verified
    spSafe := Proof.Ffdh.X86.Shape.derivePublic_spSafe
    stack := 172 },
  Spec.Ffdh.keyInitApi.artifact X86.target {
    code := Impl.Ffdh.X86.KeyInit.code
    verified := Proof.Ffdh.X86.KeyInit.verified },
  Spec.Ffdh.generateKeyApi.artifact X86.target {
    code := Impl.Ffdh.X86.GenerateKey.code
    verified := Proof.Ffdh.X86.KeyGen.verified
    spSafe := Proof.Ffdh.X86.Shape.generateKey_spSafe
    stack := 172 },
  Spec.Ffdh.keySearchApi.artifact X86.target {
    code := Impl.Ffdh.X86.KeySearch.code
    verified := Proof.Ffdh.X86.KeySearch.verified
    spSafe := Proof.Ffdh.X86.Shape.keySearch_spSafe
    stack := 220 },
  Spec.Ffdh.parameterInitApi.artifact X86.target {
    code := Impl.Ffdh.X86.ParamInit.code
    verified := Proof.Ffdh.X86.ParamInit.verified },
  Spec.Ffdh.sievedParameterSearchApi.artifact X86.target {
    code := Impl.Ffdh.X86.ParamSearch.code
    verified := Proof.Ffdh.X86.PSearch.verified
    spSafe := Proof.Ffdh.X86.Shape.paramSearch_spSafe
    consts := VG.Impl.RsaKeyGen.TrialTable32.consts
    stack := 212 }]

end VG.Artifacts.Ffdh.X86
