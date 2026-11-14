module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.CheckPublic
public import VerifiedGarbage.Proof.Ffdh.RISCV64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcCT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptCT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.SearchProof.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # Finite-field Diffie–Hellman on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ffdh.RISCV64

def artifacts : List Artifact := [
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
  Spec.Ffdh.cachedGenerateKeyApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Cached.Generate.code
    verified := Proof.Ffdh.RISCV64.Cached.cg_verified },
  Spec.Ffdh.cachedKeySearchApi.artifact RISCV64.target {
    stack := 64
    code := Proof.Ffdh.RISCV64.Cached.SearchProof.keyCode
    verified := Proof.Ffdh.RISCV64.Cached.SearchProof.search_verified }]

end VG.Artifacts.Ffdh.RISCV64
