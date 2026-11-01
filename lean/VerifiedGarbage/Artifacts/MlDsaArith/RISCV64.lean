module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.NttInv
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on RISC-V: the arithmetic of polynomials -/

@[expose] public section

namespace VG.Artifacts.MlDsaArith.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.nttApi.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Arith.ntt
    verified := Proof.MlDsa.RISCV64.Arith.Ntt.verified },
  Spec.MlDsa.nttInvApi.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Arith.nttInv
    verified := Proof.MlDsa.RISCV64.Arith.NttInv.verified },
  Spec.MlDsa.mulApi.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Arith.mul
    verified := Proof.MlDsa.RISCV64.Arith.Mul.mul_verified },
  Spec.MlDsa.mulAddApi.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Arith.mulAdd
    verified := Proof.MlDsa.RISCV64.Arith.Mul.mulAdd_verified },
  Spec.MlDsa.addApi.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Arith.add
    verified := Proof.MlDsa.RISCV64.Arith.AddSub.add_verified },
  Spec.MlDsa.subApi.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Arith.sub
    verified := Proof.MlDsa.RISCV64.Arith.AddSub.sub_verified }]

end VG.Artifacts.MlDsaArith.RISCV64
