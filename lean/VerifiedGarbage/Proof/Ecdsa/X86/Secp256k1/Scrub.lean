module

public import VerifiedGarbage.Proof.Ecdsa.X86.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Secp256k1.Lit
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
# ECDSA over secp256k1 on x86 (32-bit), without secret residue

`vg_ecdsa_secp256k1_verify` and `vg_ecdsa_secp256k1_sign`, the latter with the HMAC
implementations of SHA-1's and SHA-256's variants
(`Proof/Variants/Sha1/X86.lean`, `Proof/Variants/Sha256/X86.lean`) in its
table, each followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail`, as emitted (`X86.Scrub.verifiedScrubbedAll`), with their postconditions'
locality from `Proof/Ecdsa/X86/Scrub.lean`. The signing code's side
condition is evaluated once, of the code without the curve's proofs
(`Ecdsa.X86.Scrub.cfgOf`), with the HMAC implementations' and the curve's
literals.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.Secp256k1.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Ecdsa.X86.Scrub
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT OK secp256k1 secp256k1T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

/-- The HMAC implementations of the table. -/
abbrev vs : List HmacTable.X86.HVar :=
  vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

/-- `vg_ecdsa_secp256k1_verify`. -/
theorem verify_scrubbed (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86.Inv.InvSounds) :
    VerifiedScrubbed target Impl.Ecdsa.X86.Fn.verifySecp256k1
      (Spec.Ecdsa.Secp256k1.inst.verifyHashContract (X86.abi.withConsts Impl.Ecdsa.X86.secp256k1Comb.combConsts)
        (20 + Impl.Ecdsa.X86.VerifyHash.frameBytes)) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Secp256k1.verifyHashApi)
    { code := Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
        Impl.Ecdsa.Verify.X86.verifySecp256k1
      verified := Proof.Ecdsa.Verify.X86.Secp256k1.verifyHash_verified hL hI }
    (verifyHashOut Spec.Ecdsa.Secp256k1.inst Impl.Ecdsa.X86.secp256k1Comb.combConsts _)

/-- What the cleanup needs of `vg_ecdsa_secp256k1_sign`'s code, evaluated once. -/
theorem signSide :
    scrubFSide (Impl.Ecdsa.Rfc6979.X86.signCode (cfgOf Impl.Ecdsa.X86.secp256k1Comb false 0
      "vg_ecdsa_secp256k1_sign_k" Impl.Ecdsa.X86.signSecp256k1Comb Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs))
      [("hmac", tables vs)] Rfc6979.X86.stackT = true := by
  lit_decide

/-- `vg_ecdsa_secp256k1_sign`, with the HMAC implementations of `vs` in its table. -/
theorem sign_scrubbed (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86.Inv.InvSounds) (hv : OK vs ∧ "VG_SECP256K1_COMB" ∉ names vs) :
    VerifiedScrubbed target (Impl.Ecdsa.X86.Fn.signSecp256k1 (HmacTable.X86.fnsOf vs))
      (Rfc6979.X86.specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 Impl.Ecdsa.X86.secp256k1Comb.combConsts vs) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi)
    { tables := [("hmac", tables vs)]
      code := signCodeT (secp256k1 hL hI) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs
      verified := secp256k1T_verified hL hI vs hv
      spSafe := signCode_sp _ _ _ }
    (signOut Spec.Ecdsa.Rfc6979.Curves.secp256k1 Impl.Ecdsa.X86.secp256k1Comb.combConsts vs)
    (hs := signSide_of (R := secp256k1 hL hI) signSide)

end VG.Proof.Ecdsa.X86.Secp256k1.Scrub
