module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeVerified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcCT
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptVerified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # Finite-field Diffie–Hellman on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ffdh.PPC64LE

def direct : List Artifact := [
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
  Spec.Ffdh.generationPrecomputeApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Cached.Precompute.code
    verified := Proof.Ffdh.PPC64LE.Cached.pc_verified },
  Spec.Ffdh.cachedGenerateKeyApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Cached.Generate.code
    verified := Proof.Ffdh.PPC64LE.Cached.cg_verified },
  Spec.Ffdh.cachedKeySearchApi.artifact PPC64LE.target {
    stack := 192
    code := Proof.Ffdh.PPC64LE.Cached.SearchProof.keyCode
    verified := Proof.Ffdh.PPC64LE.Cached.SearchProof.search_verified }]

end VG.Artifacts.Ffdh.PPC64LE

-- FFDH parameter generation calls each shared Miller–Rabin implementation
namespace VG.Artifacts.Ffdh.PPC64LE.MillerRabin

def artifacts (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.Ffdh.sievedParameterSearchApi.artifact PPC64LE.target {
    suffix := v.suffix
    stack := 336
    code := Proof.Ffdh.PPC64LE.Generation.searchCode v
    verified := Proof.Ffdh.PPC64LE.Generation.search_verified v
    features := v.features }]

end VG.Artifacts.Ffdh.PPC64LE.MillerRabin

namespace VG.Artifacts.Ffdh.PPC64LE

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.flatMap fun v => MillerRabin.artifacts v)

end VG.Artifacts.Ffdh.PPC64LE
