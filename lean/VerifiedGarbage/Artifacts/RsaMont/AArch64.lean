module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified

@[expose] public section

namespace VG.Artifacts.RsaMont.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  { Spec.Rsa.Mont.mulApi with
    target := target
    doc := Spec.Rsa.Mont.mulApi.doc
      (notes := ["Baseline AArch64: coarsely integrated operand scanning with `mul` and \
        `umulh`, followed by a subtraction selected with `csel`. Uses only caller-saved \
        registers and no stack."])
    code := Impl.Bignum.AArch64.MontFn.mulBase
    contract := Spec.Rsa.Mont.mulContract abi
    verified := Proof.Bignum.AArch64.MontFn.fn_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.RsaMont.AArch64
