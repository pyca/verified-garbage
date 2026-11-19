module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.Ecdh.X86.Verified
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Proof.Ecdh.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDH over P256 on x86 (32-bit), without secret residue

`vg_ecdh_p256`, followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail` (`X86.Scrub.scrubFOf`), with its postcondition's
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86.P256.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ecdh_p256`. -/
def exchangeReg (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) (hO : Weierstrass.PrimeOrder Spec.P256.curve) :
    Registration Spec.Ecdh.P256.exchangeApi target :=
  scrubFOf {
      code := Impl.Ecdh.X86.exchangeP256
      verified := Proof.Ecdh.X86.ecdh_verified hL hI hO }
    (exchangeOut _ _ [])

end VG.Proof.Ecdh.X86.P256.Scrub
