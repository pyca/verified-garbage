module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication in the RSA working space, as a function, on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaMont.X86_64

def artifacts : List Artifact := [
  Spec.Rsa.Mont.mulApi.artifact X86_64.target {
    code := Impl.Bignum.X86_64.MontFn.mulBase
    verified := Proof.Bignum.X86_64.MontFn.fn_verified },
  Spec.Rsa.Mont.mulApi.artifact X86_64.target {
    suffix := "_adx"
    code := Impl.Bignum.X86_64.MontFn.mulAdx
    verified := Proof.Bignum.X86_64.MontFn.fnAdx_verified
    features := ["bmi2", "adx"] },
  Spec.Rsa.Mont.mulLazyApi.artifact X86_64.target {
    code := Impl.Bignum.X86_64.MontFn.mulBase
    verified := Proof.Bignum.X86_64.MontFn.fnLazy_verified },
  Spec.Rsa.Mont.mulLazyApi.artifact X86_64.target {
    suffix := "_adx"
    code := Impl.Bignum.X86_64.MontFn.mulAdxLazy
    verified := Proof.Bignum.X86_64.MontFn.fnAdxLazy_verified
    features := ["bmi2", "adx"] }]

end VG.Artifacts.RsaMont.X86_64
