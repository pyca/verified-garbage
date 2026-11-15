module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.CheckPublic
public import VerifiedGarbage.Proof.Ffdh.RISCV64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcCT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.SearchProof.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64

/-! # Finite-field Diffie–Hellman on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ffdh.RISCV64

def direct : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Generation.init
    verified := Proof.Ffdh.RISCV64.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.KeyGeneration.init
    verified := Proof.Ffdh.RISCV64.KeyGeneration.init_verified },
  Spec.Ffdh.checkPublicApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Domain.checkPublic
    verified := Proof.Ffdh.RISCV64.Domain.checkPublic_verified },
  Spec.Ffdh.checkDomainApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.VettedValidation.code
    verified := Proof.Ffdh.RISCV64.VettedValidation.verified },
  Spec.Ffdh.exchangeApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.exchange
    verified := Proof.Ffdh.RISCV64.exchange_verified },
  Spec.Ffdh.derivePublicApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Derive.derivePublic
    verified := Proof.Ffdh.RISCV64.Derive.derivePublic_verified },
  Spec.Ffdh.checkPrivateApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.CheckPrivate.checkPrivate
    verified := Proof.Ffdh.RISCV64.CheckPrivate.checkPrivate_verified },
  Spec.Ffdh.generationPrecomputeApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Cached.Precompute.code
    verified := Proof.Ffdh.RISCV64.Cached.pc_verified },
  Spec.Ffdh.cachedKeySearchApi.artifact RISCV64.target {
    code := Proof.Ffdh.RISCV64.Cached.SearchProof.keyCode
    verified := Proof.Ffdh.RISCV64.Cached.SearchProof.search_verified }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.RISCV64.variants.flatMap fun (v : Proof.MillerRabin.RISCV64.RoundImpl) => [
    Spec.Ffdh.sievedParameterSearchApi.artifact RISCV64.target {
      suffix := v.suffix
      code := Proof.Ffdh.RISCV64.Generation.searchCode v
      verified := Proof.Ffdh.RISCV64.Generation.search_verified v }])

end VG.Artifacts.Ffdh.RISCV64
