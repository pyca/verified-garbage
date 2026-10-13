module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontFnProduct
import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Artifacts.RsaMont.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  { Spec.Rsa.Mont.mulApi with
    target := target
    doc := Spec.Rsa.Mont.mulApi.doc
      (notes := ["Baseline AArch64: in-place squares of array 5 share RSA's verified scheduled eight-limb \
        Montgomery squaring kernel and blocked reduction when the public \
        width allows it. The (5, 5, 6) window product shares the eight-limb product kernel. \
        Other public index tuples use coarsely integrated operand scanning. Preserves callee-saved \
        registers using the existing workspace, with no stack."])
    code := Impl.Bignum.AArch64.MontFn.mulProduct
    contract := Spec.Rsa.Mont.mulContract abi
    verified := Proof.Bignum.AArch64.MontFn.Product.mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.RsaMont.AArch64
