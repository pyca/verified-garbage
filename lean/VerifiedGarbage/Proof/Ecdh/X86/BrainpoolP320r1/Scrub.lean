module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.Ecdh.X86.BrainpoolP320r1.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
import VerifiedGarbage.Proof.Ecdh.X86.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP320r1
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDH over BrainpoolP320r1 on x86 (32-bit), without secret residue

`vg_ecdh_brainpoolp320r1`, as emitted, followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedAll`), with its postcondition's
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86.BrainpoolP320r1.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ecdh_brainpoolp320r1`. -/
theorem exchange_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed target Impl.Ecdh.X86.Fn.exchangeBrainpoolP320r1 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP320r1.inst X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.BrainpoolP320r1.exchangeApi)
    { code := Impl.Ecdh.X86.exchangeBrainpoolP320r1
      verified := Proof.Ecdh.X86.BrainpoolP320r1.ecdh_verified hL }
    (exchangeOut _ _ [])

end VG.Proof.Ecdh.X86.BrainpoolP320r1.Scrub
