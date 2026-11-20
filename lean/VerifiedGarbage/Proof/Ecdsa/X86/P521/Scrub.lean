module

public import VerifiedGarbage.Proof.Ecdsa.X86.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P521
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ecdsa.P521.X86Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.X86.P521.CombLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Lit
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
# ECDSA over P-521 on x86 (32-bit), without secret residue

`vg_ecdsa_p521_verify` and `vg_ecdsa_p521_sign`, the latter with the HMAC
implementations of SHA-1's and SHA-256's variants
(`Proof/Variants/Sha1/X86.lean`, `Proof/Variants/Sha256/X86.lean`) in its
table, each followed by the zeroing of the stack its frames and calls use
and `Impl.Scrub.X86.tail`, as emitted (`X86.Scrub.verifiedScrubbedF`), with their postconditions'
locality from `Proof/Ecdsa/X86/Scrub.lean`. The signing code's side
condition is evaluated once, of the code without the curve's proofs
(`Ecdsa.X86.Scrub.cfgOf`), with the HMAC implementations' and the curve's
literals.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P521.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Ecdsa.X86.Scrub
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT OK p521 p521T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

/-- The HMAC implementations of the table. -/
abbrev vs : List HmacTable.X86.HVar :=
  vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

/-- `vg_ecdsa_p521_verify`. -/
theorem verify_scrubbed (hL : Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.Ecdsa.X86.Fn.verifyP521
      (Spec.Ecdsa.P521.inst.verifyHashContract (X86.abi.withConsts Impl.Ecdsa.X86.p521Comb.combConsts)
        (20 + Impl.Ecdsa.X86.VerifyHash.frameBytes)) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.P521.verifyHashApi)
    { code := Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
        Impl.Ecdsa.Verify.X86.verifyP521
      verified := Proof.Ecdsa.Verify.X86.P521.verifyHash_verified hL }
    (verifyHashOut Spec.Ecdsa.P521.inst Impl.Ecdsa.X86.p521Comb.combConsts _)

/-- What the cleanup needs of `vg_ecdsa_p521_sign`'s code, evaluated once. -/
theorem signSide :
    scrubFSide (Impl.Ecdsa.Rfc6979.X86.signCode (cfgOf Impl.Ecdsa.X86.p521Comb true 7
      "vg_ecdsa_p521_sign_k" Impl.Ecdsa.X86.signP521Comb Spec.Ecdsa.Rfc6979.Curves.p521.tries vs))
      [("hmac", tables vs)] Rfc6979.X86.stackT = true := by
  lit_decide

/-- `vg_ecdsa_p521_sign`, with the HMAC implementations of `vs` in its table. -/
theorem sign_scrubbed (hL : Weierstrass.Law Spec.P521.curve) (hv : OK vs ∧ "VG_P521_COMB" ∉ names vs) :
    VerifiedScrubbed target (Impl.Ecdsa.X86.Fn.signP521 (HmacTable.X86.fnsOf vs))
      (Rfc6979.X86.specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.X86.p521Comb.combConsts vs) 32 :=
  verifiedScrubbedF (api := Spec.Ecdsa.Rfc6979.Curves.p521SignApi)
    { tables := [("hmac", tables vs)]
      code := signCodeT (p521 hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs
      verified := p521T_verified hL vs hv
      spSafe := signCode_sp _ _ _ }
    (signOut Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.X86.p521Comb.combConsts vs)
    (hs := signSide_of (R := p521 hL) signSide)

end VG.Proof.Ecdsa.X86.P521.Scrub
