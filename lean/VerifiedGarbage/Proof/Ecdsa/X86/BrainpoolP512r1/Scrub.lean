module

public import VerifiedGarbage.Proof.Ecdsa.X86.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP512r1
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP512r1.Lit
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
# ECDSA over brainpoolP512r1 on x86 (32-bit), without secret residue

`vg_ecdsa_brainpoolp512r1_verify` and `vg_ecdsa_brainpoolp512r1_sign`, the latter with the HMAC
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

namespace VG.Proof.Ecdsa.X86.BrainpoolP512r1.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Ecdsa.X86.Scrub
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT OK brainpoolp512r1 brainpoolp512r1T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

/-- The HMAC implementations of the table. -/
abbrev vs : List HmacTable.X86.HVar :=
  vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

/-- `vg_ecdsa_brainpoolp512r1_verify`. -/
theorem verify_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    VerifiedScrubbed target Impl.Ecdsa.X86.Fn.verifyBrainpoolP512r1
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (X86.abi.withConsts Impl.Ecdsa.X86.brainpoolp512r1Comb.combConsts)
        (24 + Impl.Ecdsa.X86.VerifyHash.frameBytes)) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.BrainpoolP512r1.verifyHashApi)
    { code := Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
        Impl.Ecdsa.Verify.X86.verifyBrainpoolP512r1
      verified := Proof.Ecdsa.Verify.X86.BrainpoolP512r1.verifyHash_verified hL }
    (verifyHashOut Spec.Ecdsa.BrainpoolP512r1.inst Impl.Ecdsa.X86.brainpoolp512r1Comb.combConsts _)

/-- What the cleanup needs of `vg_ecdsa_brainpoolp512r1_sign`'s code, evaluated once. -/
theorem signSide :
    scrubFSide (Impl.Ecdsa.Rfc6979.X86.signCode (cfgOf Impl.Ecdsa.X86.brainpoolp512r1Comb false 0
      "vg_ecdsa_brainpoolp512r1_sign_k" Impl.Ecdsa.X86.signBrainpoolP512r1Comb Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs))
      [("hmac", tables vs)] Rfc6979.X86.stackT = true := by
  lit_decide

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the HMAC implementations of `vs` in its table. -/
theorem sign_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hv : OK vs ∧ "VG_BRAINPOOLP512R1_COMB" ∉ names vs) :
    VerifiedScrubbed target (Impl.Ecdsa.X86.Fn.signBrainpoolP512r1 (HmacTable.X86.fnsOf vs))
      (Rfc6979.X86.specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Ecdsa.X86.brainpoolp512r1Comb.combConsts vs) 32 :=
  verifiedScrubbedAll (api := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi)
    { tables := [("hmac", tables vs)]
      code := signCodeT (brainpoolp512r1 hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs
      verified := brainpoolp512r1T_verified hL vs hv
      spSafe := signCode_sp _ _ _ }
    (signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Ecdsa.X86.brainpoolp512r1Comb.combConsts vs)
    (hs := signSide_of (R := brainpoolp512r1 hL) signSide)

end VG.Proof.Ecdsa.X86.BrainpoolP512r1.Scrub
