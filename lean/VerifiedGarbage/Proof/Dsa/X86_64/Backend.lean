import VerifiedGarbage.Proof.Dsa.X86_64.Calls

/-! # Arithmetic variants for the complete DSA entry points

A backend supplies Montgomery arithmetic, by calls of a function
(`CallMont`), and its instruction metadata. The generic registration emits
both callers for every backend in the interface.
-/
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

structure Backend where
  call : CallMont
  suffix : String
  features : List String
  signIn : (SignVerify.sign call.mm).InlineOk = true
  verifyIn : (SignVerify.verify call.mm).InlineOk = true
  signEq : (SignVerify.sign call.mm).inline = SignVerify.sign call.mont.mm
  verifyEq : (SignVerify.verify call.mm).inline = SignVerify.verify call.mont.mm
  signMx : (SignVerify.sign call.mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  verifyMx : (SignVerify.verify call.mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  signSp : (SignVerify.sign call.mm).all (fun i => !isa.writesSp i) = true
  verifySp : (SignVerify.verify call.mm).all (fun i => !isa.writesSp i) = true

end VG.Proof.Dsa.X86_64
