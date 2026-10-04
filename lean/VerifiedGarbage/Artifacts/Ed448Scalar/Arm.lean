import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified

/-!
# Ed448 scalar arithmetic on ARMv7

The signatures and documentation come from the reviewed Ed448 API. These
building blocks reduce and combine scalars modulo the subgroup order with
baseline integer instructions; they neither hash messages nor implement
signing by themselves.
-/

namespace VG.Artifacts.Ed448Scalar.Arm

def artifacts : List Artifact := [
  { Spec.Ed448.scalarReduceApi with
    target := Arm.target
    doc := Spec.Ed448.scalarReduceApi.doc (notes := ["Processes the input from the top, \
      sixteen bits at a time, into a remainder of twenty-eight 16-bit limbs: each step folds \
      the bits above 2^446 back with one multiplication by the 224-bit 2^446 - L, using only \
      the low 32-bit `mul` instruction on 16-bit limbs, then adds 2^448 - L and selects the \
      sum or the folded value with a carry mask. Callee-saved registers are saved in the \
      first 32 bytes of `scratch`, and the output's address in the next 4."])
    code := Impl.Ed448.Arm.scalarReduce
    contract := Spec.Ed448.scalarReduceContract Arm.abi
    verified := Proof.Ed448.Arm.scalarReduce_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ed448.scalarMulAddApi with
    target := Arm.target
    doc := Spec.Ed448.scalarMulAddApi.doc (notes := ["Reduces `k`, `s` and `r` modulo L \
      as `vg_ed448_scalar_reduce` does, multiplies the first two with X448's rows of 16-bit \
      limbs (its field multiplication without the reduction), reduces the 56-limb product \
      the same way, and adds the third with a last conditional subtraction. Callee-saved \
      registers are saved in the first 32 bytes of `scratch`, and the arguments' addresses \
      in the next 16."])
    code := Impl.Ed448.Arm.scalarMulAdd
    contract := Spec.Ed448.scalarMulAddContract Arm.abi
    verified := Proof.Ed448.Arm.scalarMulAdd_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448Scalar.Arm
