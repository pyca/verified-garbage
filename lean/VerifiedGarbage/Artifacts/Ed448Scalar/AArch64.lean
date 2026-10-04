import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified

/-!
# Ed448 scalar arithmetic on AArch64

The signatures and documentation come from the reviewed Ed448 API. These
building blocks reduce and combine scalars modulo the subgroup order with
baseline integer instructions; they neither hash messages nor implement
signing by themselves.
-/

namespace VG.Artifacts.Ed448Scalar.AArch64

def artifacts : List Artifact := [
  { Spec.Ed448.scalarReduceApi with
    target := AArch64.target
    doc := Spec.Ed448.scalarReduceApi.doc (notes := ["Processes the input from the top, \
      a 64-bit word at a time, into a seven-word remainder: each step folds the bits above \
      2^446 back with one 64x224-bit product (`mul` and `umulh` by the words of \
      `2^446 - L`), then adds 2^448 - L and selects the sum or the folded value with a \
      carry mask. Callee-saved registers are saved in the first 64 bytes of `scratch`."])
    code := Impl.Ed448.AArch64.scalarReduce
    contract := Spec.Ed448.scalarReduceContract AArch64.abi
    verified := Proof.Ed448.AArch64.scalarReduce_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ed448.scalarMulAddApi with
    target := AArch64.target
    doc := Spec.Ed448.scalarMulAddApi.doc (notes := ["Copies `k`, `r` and `s` to `scratch` \
      as eight words each, forms the complete 16-word `r + k*s` by product scanning, and \
      reduces it modulo L a 64-bit word at a time as `vg_ed448_scalar_reduce` does. \
      Callee-saved registers are saved in the first 64 bytes of `scratch`."])
    code := Impl.Ed448.AArch64.scalarMulAdd
    contract := Spec.Ed448.scalarMulAddContract AArch64.abi
    verified := Proof.Ed448.AArch64.scalarMulAdd_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448Scalar.AArch64
