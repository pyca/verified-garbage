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
    notes := ["Uses only caller-saved registers and no stack. The function reduces all 912 input \
      bits from the top, one at a time, in fourteen 32-bit limbs in `scratch` (rounded up to a \
      multiple of 8): the remainder doubled with the bit as the carry in, then `L` subtracted (as \
      an addition of `2^448 - L`, whose carry out says whether the remainder was at least `L`) and \
      selected with a mask. The result is written a byte at a time."]
    code := Impl.Ed448.RISCV64.scalarReduce
    verified := Proof.Ed448.RISCV64.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact RISCV64.target {
    notes := ["Uses only caller-saved registers and no stack. The function reduces `k`, `s` and \
      `r` modulo `L` as `vg_ed448_scalar_reduce` does, computes the 896-bit product of the first \
      two row by row with `mul` (X448's RISC-V product, without its reduction), adds the third, \
      and reduces the sum the same way. The result is written a byte at a time."]
    code := Impl.Ed448.RISCV64.scalarMulAdd
    verified := Proof.Ed448.RISCV64.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.RISCV64
