module

public import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 scalar arithmetic on ARMv7

The signatures and documentation come from the reviewed Ed448 API. These
building blocks reduce and combine scalars modulo the subgroup order with
baseline integer instructions; they neither hash messages nor implement
signing by themselves.
-/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.Arm

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact Arm.target {
    notes := ["Processes the input from the top, \
      sixteen bits at a time, into a remainder of twenty-eight 16-bit limbs: each step folds \
      the bits above 2^446 back with one multiplication by the 224-bit 2^446 - L, using only \
      the low 32-bit `mul` instruction on 16-bit limbs, then adds 2^448 - L and selects the \
      sum or the folded value with a carry mask. Callee-saved registers are saved in the \
      first 32 bytes of `scratch`, and the output's address in the next 4."]
    code := Impl.Ed448.Arm.scalarReduce
    verified := Proof.Ed448.Arm.scalarReduce_verified
    stack := 0 },
  Spec.Ed448.scalarMulAddApi.artifact Arm.target {
    notes := ["Reduces `k`, `s` and `r` modulo L \
      as `vg_ed448_scalar_reduce` does, multiplies the first two with X448's rows of 16-bit \
      limbs (its field multiplication without the reduction), reduces the 56-limb product \
      the same way, and adds the third with a last conditional subtraction. Callee-saved \
      registers are saved in the first 32 bytes of `scratch`, and the arguments' addresses \
      in the next 16."]
    code := Impl.Ed448.Arm.scalarMulAdd
    verified := Proof.Ed448.Arm.scalarMulAdd_verified
    stack := 0 }]

end VG.Artifacts.Ed448Scalar.Arm
