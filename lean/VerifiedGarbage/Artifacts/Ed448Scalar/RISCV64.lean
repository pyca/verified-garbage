module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 scalar arithmetic on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.RISCV64

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.scalarReduce
    verified := Proof.Ed448.RISCV64.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.scalarMulAdd
    verified := Proof.Ed448.RISCV64.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.RISCV64
