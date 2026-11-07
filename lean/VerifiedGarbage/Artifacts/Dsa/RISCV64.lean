module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParameterSearchInit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # DSA on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Dsa.RISCV64

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Derive.derive
    verified := Proof.Dsa.RISCV64.deriveKey_verified },
  Spec.Dsa.validatePrivateKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.PrevalidatedSign.validate
    verified := Proof.Dsa.RISCV64.validatePrivate_verified },
  Spec.Dsa.randomSignPrevalidatedApi.artifact RISCV64.target {
    stack := 192
    code := Impl.Dsa.RISCV64.PrevalidatedSign.randomSign
    verified := Proof.Dsa.RISCV64.randomSignPre_verified },
  Spec.Dsa.generateKeyApi.artifact RISCV64.target {
    stack := 192
    code := Impl.Dsa.RISCV64.Generate.code
    verified := Proof.Dsa.RISCV64.generateKey_verified },
  Spec.Dsa.validatePublicKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Prevalidated.validate
    verified := Proof.Dsa.RISCV64.validate_verified },
  Spec.Dsa.verifyPrevalidatedApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Prevalidated.verify
    verified := Proof.Dsa.RISCV64.prevalidated_verified },
  Spec.Dsa.parameterInitApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.ParameterSearch.init
    verified := Proof.Dsa.RISCV64.init_verified }]

end VG.Artifacts.Dsa.RISCV64
