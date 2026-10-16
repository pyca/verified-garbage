module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontFnProduct
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.RsaMont.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  Spec.Rsa.Mont.mulApi.artifact target {
    notes := ["Baseline AArch64: in-place squares of array 5 share RSA's verified scheduled eight-limb \
        Montgomery squaring kernel and blocked reduction when the public \
        width allows it. The (5, 5, 6) window product shares the eight-limb product kernel. \
        Other public index tuples use coarsely integrated operand scanning. Preserves callee-saved \
        registers using the existing workspace, with no stack."]
    code := Impl.Bignum.AArch64.MontFn.mulProduct
    verified := Proof.Bignum.AArch64.MontFn.Product.mul_verified }]

end VG.Artifacts.RsaMont.AArch64
