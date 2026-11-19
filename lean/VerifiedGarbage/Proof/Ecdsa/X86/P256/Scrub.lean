module

public import VerifiedGarbage.Proof.Ecdsa.X86.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P256
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombVerified
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombFunction
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
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
# ECDSA over P-256 on x86 (32-bit), without secret residue

`vg_ecdsa_p256_verify` and `vg_ecdsa_p256_sign`, the latter with the HMAC
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

namespace VG.Proof.Ecdsa.X86.P256.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Ecdsa.X86.Scrub
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT OK p256 p256T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

/-- The HMAC implementations of the table. -/
abbrev vs : List HmacTable.X86.HVar :=
  vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

/-- `vg_ecdsa_p256_verify`. -/
def verifyReg (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) :
    Registration Spec.Ecdsa.P256.verifyHashApi target :=
  scrubFOf {
      code := Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
        Proof.Ecdsa.Verify.X86.vCombCode
      verified := Proof.Ecdsa.Verify.X86.vCombHash_verified hL hI }
    (verifyHashOut Spec.Ecdsa.P256.inst Impl.Ecdsa.X86.p256Comb.combConsts _)

/-- What `scrubFOf` needs of `vg_ecdsa_p256_sign`'s code, evaluated once. -/
theorem signSide :
    scrubFSide (Impl.Ecdsa.Rfc6979.X86.signCode (cfgOf Impl.Ecdsa.X86.p256Comb false 0
      "vg_ecdsa_p256_sign_k" Impl.Ecdsa.X86.signP256Comb Spec.Ecdsa.Rfc6979.Curves.p256.tries vs))
      [("hmac", tables vs)] Rfc6979.X86.stackT = true := by
  lit_decide

/-- `vg_ecdsa_p256_sign`. -/
def signReg (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds)
    (hv : OK vs ∧ "VG_P256_COMB" ∉ names vs) :
    Registration Spec.Ecdsa.Rfc6979.Curves.p256SignApi target :=
  scrubFOf {
      tables := [("hmac", tables vs)]
      code := signCodeT (p256 hL hI) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs
      verified := p256T_verified hL hI vs hv
      spSafe := signCode_sp _ _ _ }
    (signOut Spec.Ecdsa.Rfc6979.Curves.p256 Impl.Ecdsa.X86.p256Comb.combConsts vs)
    Rfc6979.X86.stackT (signSide_of (R := p256 hL hI) signSide)

end VG.Proof.Ecdsa.X86.P256.Scrub
