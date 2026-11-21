module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # DSA (FIPS 186-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Dsa.RISCV64

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.deriveKey
    verified := Proof.Dsa.RISCV64.Fn.deriveKey },
  Spec.Dsa.validatePrivateKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.validatePrivateKey
    verified := Proof.Dsa.RISCV64.Fn.validatePrivateKey },
  Spec.Dsa.randomSignPrevalidatedApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.randomSignPrevalidated
    verified := Proof.Dsa.RISCV64.Fn.randomSignPrevalidated },
  Spec.Dsa.generateKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.generateKey
    verified := Proof.Dsa.RISCV64.Fn.generateKey },
  Spec.Dsa.validatePublicKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.validatePublicKey
    verified := Proof.Dsa.RISCV64.Fn.validatePublicKey },
  Spec.Dsa.verifyPrevalidatedApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.verifyPrevalidated
    verified := Proof.Dsa.RISCV64.Fn.verifyPrevalidated },
  Spec.Dsa.parameterInitApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.parameterInit
    verified := Proof.Dsa.RISCV64.Fn.parameterInit }] ++
  Proof.Variants.MillerRabin.RISCV64.variants.map fun (v : Proof.MillerRabin.RISCV64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact RISCV64.target {
      suffix := v.suffix
      code := Impl.Dsa.RISCV64.Fn.parameterSearch v.suffix v.code
      verified := Proof.Dsa.RISCV64.Fn.parameterSearch v }

end VG.Artifacts.Dsa.RISCV64
