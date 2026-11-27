module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.RISCV64.Fn
import VerifiedGarbage.Proof.Rsa.RISCV64.IbInverse
import VerifiedGarbage.Proof.Divstep.TcSBounds
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSA (RFC 8017) on RISC-V -/

namespace VG.Artifacts.Rsa.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Rsa.publicPrecomputeApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.publicPrecompute
    verified := Proof.Rsa.RISCV64.Fn.publicPrecompute },
  Spec.Rsa.privatePrecomputeApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.privatePrecompute
    verified := Proof.Rsa.RISCV64.Fn.privatePrecompute },
  Spec.Rsa.crtValuesApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.crtValues
    verified := Proof.Rsa.RISCV64.Fn.crtValues },
  Spec.Rsa.checkKeyApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.checkKey
    verified := Proof.Rsa.RISCV64.Fn.checkKey },
  Spec.Rsa.recoverPrimesDetApi.artifact RISCV64.target {
    code := Impl.Rsa.RISCV64.Fn.recoverPrimesDet
    verified := Proof.Rsa.RISCV64.Fn.recoverPrimesDet }]

spec_apis artifacts

end VG.Artifacts.Rsa.RISCV64
