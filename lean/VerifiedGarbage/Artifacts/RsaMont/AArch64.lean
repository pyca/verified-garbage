module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontFnProduct
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.RsaMont.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  Spec.Rsa.Mont.mulApi.artifact target {
    code := Impl.Bignum.AArch64.MontFn.mulProduct
    verified := Proof.Bignum.AArch64.MontFn.Product.mul_verified }]

end VG.Artifacts.RsaMont.AArch64
