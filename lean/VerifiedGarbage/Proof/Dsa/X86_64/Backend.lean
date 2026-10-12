import VerifiedGarbage.Proof.Dsa.X86_64.Calls

/-! # Arithmetic variants for the complete DSA entry points

A backend supplies Montgomery multiplication, inline or by calls of a function
(`mm`, which inlines to `mont.mm`), and its instruction metadata. The generic
registration emits both callers for every backend in the interface.
-/
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Proof.Bignum.X86_64

structure Backend where
  mm : Nat → Nat → Nat → Prog isa
  mont : Mont
  /-- How the backend multiplies, for the documentation. -/
  note : String
  suffix : String
  features : List String
  signIn : (SignVerify.sign mm).InlineOk = true
  verifyIn : (SignVerify.verify mm).InlineOk = true
  signEq : (SignVerify.sign mm).inline = SignVerify.sign mont.mm
  verifyEq : (SignVerify.verify mm).inline = SignVerify.verify mont.mm
  signMx : (SignVerify.sign mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  verifyMx : (SignVerify.verify mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  signSp : (SignVerify.sign mm).all (fun i => !isa.writesSp i) = true
  verifySp : (SignVerify.verify mm).all (fun i => !isa.writesSp i) = true

end VG.Proof.Dsa.X86_64
