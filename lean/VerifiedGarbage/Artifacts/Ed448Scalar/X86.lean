module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 scalar arithmetic on x86 (32-bit)

The signatures and documentation come from the reviewed Ed448 API. These
building blocks reduce and combine scalars modulo the subgroup order with
baseline integer instructions; they neither hash messages nor implement
signing by themselves.
-/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.X86

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact X86.target {
    notes := ["Processes the input from the top, \
      sixteen bits at a time, into a remainder of twenty-eight 16-bit limbs (X448's \
      representation on this target): each step folds the bits above 2^446 back with one \
      multiplication by the 224-bit 2^446 - L, using `mul` only on 16-bit limbs, then adds \
      2^448 - L and selects the sum or the folded value with a carry mask. Callee-saved \
      registers are saved in the first 16 bytes of `scratch`."]
    code := Impl.Ed448.X86.scalarReduce
    verified := Proof.Ed448.X86.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact X86.target {
    notes := ["Reduces `k`, `s` and `r` modulo L \
      as `vg_ed448_scalar_reduce` does, multiplies the first two with X448's rows of 16-bit \
      limbs (its field multiplication without the reduction), reduces the 56-limb product \
      the same way, and adds the third with a last conditional subtraction. Callee-saved \
      registers are saved in the first 16 bytes of `scratch`."]
    code := Impl.Ed448.X86.scalarMulAdd
    verified := Proof.Ed448.X86.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.X86
