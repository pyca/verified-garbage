module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontFnSquare

@[expose] public section

namespace VG.Artifacts.RsaMont.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  { Spec.Rsa.Mont.mulApi with
    target := target
    doc := Spec.Rsa.Mont.mulApi.doc
      (notes := ["Baseline AArch64: in-place squares of array 5 share RSA's verified symmetric \
        Montgomery squaring kernel (with its public small-size fallback). Other public \
        index tuples use coarsely integrated operand scanning. Uses only caller-saved \
        registers and the existing workspace, with no stack."])
    code := Impl.Bignum.AArch64.MontFn.mul
    contract := Spec.Rsa.Mont.mulContract abi
    verified := Proof.Bignum.AArch64.MontFn.mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.RsaMont.AArch64
