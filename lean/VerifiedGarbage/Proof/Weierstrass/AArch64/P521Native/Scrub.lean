module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeVerified
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Proof.P521.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.P521

/-!
# P-521's ECDH on AArch64, without secret residue

`vg_ecdh_p521`, the native P-521 exchange, under the shared ECDH contract with
its stack of 3456 bytes (`nativeContract`), whose postcondition reads the
memory on return only within `out` (`EcKey.AArch64.Scrub.exchangeOkW`):
returns with every register it may leave secret cleared and its whole stack
zeroed (`ScrubAll.withScrubAll`). The registration is built here, with its
stack stated, for the registration file to bind.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.P521Native.Scrub

open VG.Proof.P521.AArch64 (hasLaw)

/-- `vg_ecdh_p521`, scrubbed. -/
def exchangeReg : Registration Spec.Ecdh.P521.exchangeApi AArch64.target :=
  AArch64.ScrubAll.withScrubAll {
    code := Impl.Weierstrass.AArch64.P521Native.exchange
    verified := native_verified hasLaw.law hasLaw.inv hasLaw.prime
    consts := []
    stack := 3456 } (EcKey.AArch64.Scrub.exchangeOkW Spec.EcKey.P521.inst 3456)

end VG.Proof.Weierstrass.AArch64.P521Native.Scrub
