module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.Ecdh.X86.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Proof.Ecdh.X86.Secp256k1.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDH over Secp256k1 on x86 (32-bit), without secret residue

`vg_ecdh_secp256k1`, as emitted, followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedAll`), with its postcondition's
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86.Secp256k1.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ecdh_secp256k1`. -/
theorem exchange_scrubbed (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86.Inv.InvSounds) :
    VerifiedScrubbed target Impl.Ecdh.X86.Fn.exchangeSecp256k1 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.Secp256k1.inst X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdh.Secp256k1.exchangeApi)
    { code := Impl.Ecdh.X86.exchangeSecp256k1
      verified := Proof.Ecdh.X86.Secp256k1.ecdh_verified hL hI }
    (exchangeOut _ _ [])

end VG.Proof.Ecdh.X86.Secp256k1.Scrub
