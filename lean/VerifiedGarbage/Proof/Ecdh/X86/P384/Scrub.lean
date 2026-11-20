module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.Ecdh.X86.P384.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ecdh.P384.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Proof.Ecdh.X86.P384.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDH over P384 on x86 (32-bit), without secret residue

`vg_ecdh_p384`, as emitted, followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedF`), with its postcondition's
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86.P384.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ecdh_p384`. -/
theorem exchange_scrubbed (hL : Weierstrass.Law Spec.P384.curve) :
    VerifiedScrubbed target Impl.Ecdh.X86.Fn.exchangeP384 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst X86.abi 28) 32 :=
  verifiedScrubbedF (api := Spec.Ecdh.P384.exchangeApi)
    { code := Impl.Ecdh.X86.exchangeP384
      verified := Proof.Ecdh.X86.P384.ecdh_verified hL }
    (exchangeOut _ _ [])

end VG.Proof.Ecdh.X86.P384.Scrub
