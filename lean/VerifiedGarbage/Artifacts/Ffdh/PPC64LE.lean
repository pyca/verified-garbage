module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeVerified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Verified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Finite-field Diffie–Hellman on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ffdh.PPC64LE

def artifacts : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Generation.init
    verified := Proof.Ffdh.PPC64LE.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.KeyGeneration.init
    verified := Proof.Ffdh.PPC64LE.KeyGeneration.init_verified },
  Spec.Ffdh.checkPublicApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Domain.checkPublic
    verified := Proof.Ffdh.PPC64LE.Domain.cp_verified },
  Spec.Ffdh.checkDomainApi.artifact PPC64LE.target {
    consts := Impl.Ffdh.PPC64LE.VettedValidation.tableConsts
    code := Impl.Ffdh.PPC64LE.VettedValidation.code
    verified := Proof.Ffdh.PPC64LE.VettedValidation.verified },
  Spec.Ffdh.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Domain.exchange
    verified := Proof.Ffdh.PPC64LE.Domain.ex_verified },
  Spec.Ffdh.derivePublicApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Derive.derivePublic
    verified := Proof.Ffdh.PPC64LE.Derive.dp_verified },
  Spec.Ffdh.checkPrivateApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.CheckPrivate.checkPrivate
    verified := Proof.Ffdh.PPC64LE.CheckPrivate.kp_verified },
  Spec.Ffdh.generateKeyApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.GenerateKey.generateKey
    verified := Proof.Ffdh.PPC64LE.GenerateKey.gk_verified },
  Spec.Ffdh.keySearchApi.artifact PPC64LE.target {
    stack := 176
    code := Proof.Ffdh.PPC64LE.KeyGeneration.keyCode
    verified := Proof.Ffdh.PPC64LE.KeyGeneration.key_verified }]

end VG.Artifacts.Ffdh.PPC64LE
