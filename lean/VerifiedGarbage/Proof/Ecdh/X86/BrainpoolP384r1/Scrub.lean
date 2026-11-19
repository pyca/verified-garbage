module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.Ecdh.X86.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdh.X86.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP384r1
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDH over BrainpoolP384r1 on x86 (32-bit), without secret residue

`vg_ecdh_brainpoolp384r1`, followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail` (`X86.Scrub.scrubFOf`), with its postcondition's
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86.BrainpoolP384r1.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ecdh_brainpoolp384r1`. -/
def exchangeReg (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) :
    Registration Spec.Ecdh.BrainpoolP384r1.exchangeApi target :=
  scrubFOf {
      code := Impl.Ecdh.X86.exchangeBrainpoolP384r1
      verified := Proof.Ecdh.X86.BrainpoolP384r1.ecdh_verified hL }
    (exchangeOut _ _ [])

end VG.Proof.Ecdh.X86.BrainpoolP384r1.Scrub
