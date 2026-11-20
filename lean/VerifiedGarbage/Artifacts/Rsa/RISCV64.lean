module

public import VerifiedGarbage.Proof.Rsa.RISCV64.Fn
public import VerifiedGarbage.Proof.Rsa.RISCV64.IbInverse
public import VerifiedGarbage.Proof.Divstep.TcSBounds
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSA (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rsa.RISCV64

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.publicPrecompute
    verified := .scrubbed Proof.Rsa.RISCV64.Fn.publicPrecompute },
  Spec.Rsa.privatePrecomputeApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.privatePrecompute
    verified := .scrubbed Proof.Rsa.RISCV64.Fn.privatePrecompute },
  Spec.Rsa.crtValuesApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.crtValues
    verified := .scrubbed Proof.Rsa.RISCV64.Fn.crtValues },
  Spec.Rsa.checkKeyApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.checkKey
    verified := .scrubbed Proof.Rsa.RISCV64.Fn.checkKey },
  Spec.Rsa.recoverPrimesDetApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.recoverPrimesDet
    verified := .scrubbed Proof.Rsa.RISCV64.Fn.recoverPrimesDet }]

end VG.Artifacts.Rsa.RISCV64
