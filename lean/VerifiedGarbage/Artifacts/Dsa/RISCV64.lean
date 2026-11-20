module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # DSA (FIPS 186-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Dsa.RISCV64

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.deriveKey
    verified := .scrubbed Proof.Dsa.RISCV64.Fn.deriveKey },
  Spec.Dsa.validatePrivateKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.validatePrivateKey
    verified := .scrubbed Proof.Dsa.RISCV64.Fn.validatePrivateKey },
  Spec.Dsa.randomSignPrevalidatedApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.randomSignPrevalidated
    verified := .scrubbed Proof.Dsa.RISCV64.Fn.randomSignPrevalidated },
  Spec.Dsa.generateKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.generateKey
    verified := .scrubbed Proof.Dsa.RISCV64.Fn.generateKey },
  Spec.Dsa.validatePublicKeyApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.validatePublicKey
    verified := .scrubbed Proof.Dsa.RISCV64.Fn.validatePublicKey },
  Spec.Dsa.verifyPrevalidatedApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.verifyPrevalidated
    verified := .scrubbed Proof.Dsa.RISCV64.Fn.verifyPrevalidated },
  Spec.Dsa.parameterInitApi.artifact RISCV64.target {
    code := Impl.Dsa.RISCV64.Fn.parameterInit
    verified := .scrubbed Proof.Dsa.RISCV64.Fn.parameterInit }] ++
  Proof.Dsa.RISCV64.Fn.parameterSearchRegs.map (Spec.Dsa.parameterSearchApi.artifact RISCV64.target)

end VG.Artifacts.Dsa.RISCV64
