module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 scalar arithmetic on RISC-V

The signatures and documentation come from the reviewed Ed448 API. These
building blocks reduce and combine scalars modulo the subgroup order with
baseline integer instructions; they neither hash messages nor implement
signing by themselves.
-/

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
