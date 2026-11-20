module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.Ecdh.X86.P192.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ecdh.P192.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P192
import VerifiedGarbage.Proof.Ecdh.X86.P192.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDH over P192 on x86 (32-bit), without secret residue

`vg_ecdh_p192`, as emitted, followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedF`), with its postcondition's
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86.P192.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ecdh_p192`. -/
theorem exchange_scrubbed (hL : Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.Ecdh.X86.Fn.exchangeP192 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P192.inst X86.abi 28) 32 :=
  verifiedScrubbedF (api := Spec.Ecdh.P192.exchangeApi)
    { code := Impl.Ecdh.X86.exchangeP192
      verified := Proof.Ecdh.X86.P192.ecdh_verified hL }
    (exchangeOut _ _ [])

end VG.Proof.Ecdh.X86.P192.Scrub
