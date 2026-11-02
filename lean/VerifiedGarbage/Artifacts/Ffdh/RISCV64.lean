module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.CheckPublic
public import VerifiedGarbage.Proof.Ffdh.RISCV64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.GenerateKey.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Init
public import VerifiedGarbage.Proof.Framework.Registration

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
  Spec.Ffdh.exchangeApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.exchange
    verified := Proof.Ffdh.RISCV64.exchange_verified },
  Spec.Ffdh.derivePublicApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Derive.derivePublic
    verified := Proof.Ffdh.RISCV64.Derive.derivePublic_verified },
  Spec.Ffdh.checkPrivateApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.CheckPrivate.checkPrivate
    verified := Proof.Ffdh.RISCV64.CheckPrivate.checkPrivate_verified },
  Spec.Ffdh.generateKeyApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.GenerateKey.generateKey
    verified := Proof.Ffdh.RISCV64.GenerateKey.generateKey_verified },
  Spec.Ffdh.keySearchApi.artifact RISCV64.target {
    stack := 48
    code := Proof.Ffdh.RISCV64.KeyGeneration.keyCode
    verified := Proof.Ffdh.RISCV64.KeyGeneration.key_verified },
  Spec.Ffdh.checkPublicApi.artifact RISCV64.target {
    code := Impl.Ffdh.RISCV64.Domain.checkPublic
    verified := Proof.Ffdh.RISCV64.Domain.checkPublic_verified },
  Spec.Ffdh.checkDomainApi.artifact RISCV64.target {
    consts := Impl.Ffdh.RISCV64.VettedValidation.tableConsts
    code := Impl.Ffdh.RISCV64.VettedValidation.code
    verified := Proof.Ffdh.RISCV64.VettedValidation.verified }]

end VG.Artifacts.Ffdh.RISCV64
