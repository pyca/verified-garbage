import VerifiedGarbage.Proof.Weierstrass.X86_64.P384Literals
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64

/-!
# ECDSA verification over P-384 on x86-64: the shared code's literals

Verification's configurations (`p384v`, `p384vx`) are signing's with
`pubVerify` set, which the powers and the key's validation do not read: their
code is that of `P384Literals`, whose literals these restate (by definitional
unfolding, cheaply) where verification's code writes them, so that its
literals and checks read them rather than having the kernel build the code
again.
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64
open VG.Proof.Weierstrass.X86_64

noncomputable abbrev nPowV.lit := P384Literals.nPow.lit
theorem nPowV.lit_eq : Cfg.nPow p384v = nPowV.lit := P384Literals.nPow.lit_eq
noncomputable abbrev pPowV.lit := P384Literals.pPow.lit
theorem pPowV.lit_eq : Cfg.pPow p384v = pPowV.lit := P384Literals.pPow.lit_eq
noncomputable abbrev validateV.lit := P384Literals.validate.lit
theorem validateV.lit_eq : Impl.Ecdh.X86_64.Cfg.validate p384v = validateV.lit :=
  P384Literals.validate.lit_eq

noncomputable abbrev nPowVAdx.lit := P384Literals.nPowAdx.lit
theorem nPowVAdx.lit_eq : Cfg.nPow p384vx = nPowVAdx.lit := P384Literals.nPowAdx.lit_eq
noncomputable abbrev pPowVAdx.lit := P384Literals.pPowAdx.lit
theorem pPowVAdx.lit_eq : Cfg.pPow p384vx = pPowVAdx.lit := P384Literals.pPowAdx.lit_eq
noncomputable abbrev validateVAdx.lit := P384Literals.validateAdx.lit
theorem validateVAdx.lit_eq : Impl.Ecdh.X86_64.Cfg.validate p384vx = validateVAdx.lit :=
  P384Literals.validateAdx.lit_eq

end VG.Proof.Ecdsa.Verify.X86_64.P384
