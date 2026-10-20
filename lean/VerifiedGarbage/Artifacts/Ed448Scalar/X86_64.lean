module

public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 scalar arithmetic on x86-64

The signatures and documentation come from the reviewed Ed448 API. These
building blocks reduce and combine scalars modulo the subgroup order with
baseline integer instructions; they neither hash messages nor implement
signing by themselves.
-/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.X86_64

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact X86_64.target {
    notes := ["Processes the input from the top, \
      a 64-bit word at a time, into a seven-word remainder: each step folds the bits above \
      2^446 back with one 64x224-bit product, then adds 2^448 - L and selects the sum or the \
      saved remainder with a carry mask. Callee-saved registers are saved in the first 48 \
      bytes of `scratch`, and the output's address in the next 8."]
    code := Impl.Ed448.X86_64.scalarReduce
    verified := Proof.Ed448.X86_64.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact X86_64.target {
    notes := ["Reduces `k`, `s` and `r` modulo L \
      as `vg_ed448_scalar_reduce` does, multiplies the first two by product scanning \
      (X448's field multiplication without its reduction), reduces the 14-word product the \
      same way, and adds the third with a last conditional subtraction. Callee-saved \
      registers are saved in the first 48 bytes of `scratch`, and the arguments' addresses \
      in the next 32."]
    code := Impl.Ed448.X86_64.scalarMulAdd
    verified := Proof.Ed448.X86_64.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.X86_64
