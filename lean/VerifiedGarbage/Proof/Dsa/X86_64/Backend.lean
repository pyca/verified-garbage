import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified

/-! # Arithmetic variants for the complete DSA entry points

A backend supplies Montgomery arithmetic and its instruction metadata. The
generic registration emits both callers for every backend in the interface.
-/
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Proof.Bignum.X86_64

structure Backend where
  mont : Mont
  suffix : String
  features : List String
  signMx : (SignVerify.sign mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  verifyMx : (SignVerify.verify mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  signSp : (SignVerify.sign mont.mm).all (fun i => !isa.writesSp i) = true
  verifySp : (SignVerify.verify mont.mm).all (fun i => !isa.writesSp i) = true

end VG.Proof.Dsa.X86_64
