module

public import VerifiedGarbage.Proof.Ecdsa.X86.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P224
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P224.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.X86.P224.CombLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P224.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA over P-224 on x86 (32-bit), without secret residue

`vg_ecdsa_p224_verify` and `vg_ecdsa_p224_sign`, the latter with the HMAC
implementations of SHA-1's and SHA-256's variants
(`Proof/Variants/Sha1/X86.lean`, `Proof/Variants/Sha256/X86.lean`) in its
table, each followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail` (`X86.Scrub.scrubFOf`), with their postconditions'
locality from `Proof/Ecdsa/X86/Scrub.lean`. The signing code's side
condition is evaluated once, of the code without the curve's proofs
(`Ecdsa.X86.Scrub.cfgOf`), with the HMAC implementations' and the curve's
literals.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P224.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Ecdsa.X86.Scrub
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT OK p224 p224T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

/-- The HMAC implementations of the table. -/
abbrev vs : List HmacTable.X86.HVar :=
  vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

/-- `vg_ecdsa_p224_verify`. -/
def verifyReg (hL : Weierstrass.Law Spec.P224.curve) :
    Registration Spec.Ecdsa.P224.verifyHashApi target :=
  scrubFOf {
      code := Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
        Impl.Ecdsa.Verify.X86.verifyP224
      verified := Proof.Ecdsa.Verify.X86.P224.verifyHash_verified hL }
    (verifyHashOut Spec.Ecdsa.P224.inst Impl.Ecdsa.X86.p224Comb.combConsts _)

/-- What `scrubFOf` needs of `vg_ecdsa_p224_sign`'s code, evaluated once. -/
theorem signSide :
    scrubFSide (Impl.Ecdsa.Rfc6979.X86.signCode (cfgOf Impl.Ecdsa.X86.p224Comb false 0
      "vg_ecdsa_p224_sign_k" Impl.Ecdsa.X86.signP224Comb Spec.Ecdsa.Rfc6979.Curves.p224.tries vs))
      [("hmac", tables vs)] Rfc6979.X86.stackT = true := by
  lit_decide

/-- `vg_ecdsa_p224_sign`. -/
def signReg (hL : Weierstrass.Law Spec.P224.curve)
    (hv : OK vs ∧ "VG_P224_COMB" ∉ names vs) :
    Registration Spec.Ecdsa.Rfc6979.Curves.p224SignApi target :=
  scrubFOf {
      tables := [("hmac", tables vs)]
      code := signCodeT (p224 hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs
      verified := p224T_verified hL vs hv
      spSafe := signCode_sp _ _ _ }
    (signOut Spec.Ecdsa.Rfc6979.Curves.p224 Impl.Ecdsa.X86.p224Comb.combConsts vs)
    Rfc6979.X86.stackT (signSide_of (R := p224 hL) signSide)

end VG.Proof.Ecdsa.X86.P224.Scrub
