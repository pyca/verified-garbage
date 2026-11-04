module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateVerified
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Dsa.RISCV64

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Derive.derive
    verified := Proof.Dsa.RISCV64.deriveKey_verified },
  Spec.Dsa.randomSignApi.artifact RISCV64.target {
    stack := 192
    code := Impl.Dsa.RISCV64.RandomSign.code
    verified := Proof.Dsa.RISCV64.randomSign_verified },
  Spec.Dsa.generateKeyApi.artifact RISCV64.target {
    stack := 192
    code := Impl.Dsa.RISCV64.Generate.code
    verified := Proof.Dsa.RISCV64.generateKey_verified },
  Spec.Dsa.validatePublicKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Prevalidated.validate
    verified := Proof.Dsa.RISCV64.validate_verified },
  Spec.Dsa.verifyPrevalidatedApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Prevalidated.verify
    verified := Proof.Dsa.RISCV64.prevalidated_verified }]

end VG.Artifacts.Dsa.RISCV64
