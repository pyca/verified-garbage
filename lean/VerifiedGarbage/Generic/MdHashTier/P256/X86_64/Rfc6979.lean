module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P256Any
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-256 on x86-64, with the hash function as an argument

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_ecdsa_p256_rfc6979_sign`, calling HMAC's `init` and `finalize` and the
streaming `update` of the hash function its argument `hash` names, each of
the tier's implementation (`Variants/MdHashTier/X86_64/`), and
`vg_ecdsa_p256_sign`, is emitted for every tier, named by `Emit.qualifiedName`
(the tier's suffix, tagged `hash`), and needs the tier's CPU features. It is
generic over P-256's group law and inversions too, the variant
`Variants/P256/X86_64/Law.lean`. It is emitted for each multiplication of
`vg_ecdsa_p256_sign`: the baseline's, and BMI2's and ADX's (`vg_ecdsa_p256_sign_adx`,
which the instances with the suffix `_adx` call).

The stack is 544 bytes: a 520-byte frame, and the 24 bytes below it that the
calls use.

It reads the comb's tables of `vg_ecdsa_p256_sign`, the static `VG_P256_COMB`.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.P256.X86_64.Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (sign_spSafe anyNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P256Any (any sign_verified)

/-- The signature with the tier `t`, and P-256's multiplication with BMI2 and
ADX (`adx`, `_adx`, calling `vg_ecdsa_p256_sign_adx`) or not. -/
def withMul (t : Proof.Pbkdf2.Md.X86_64.Tier) (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve)
    (adx : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.P256Sha256.inst.signAnyApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix)] ++ (if adx then "_adx" else "")
    notes := [anyNotes 32 (Spec.Ecdsa.P256.signApi.name ++ (if adx then "_adx" else ""))]
    code := (any adx h.law (Proof.P256.combOk7 h.law) h.inv t).code
    consts := Impl.Ecdsa.X86_64.p256.combConsts
    stack := 544
    verified := sign_verified adx h.law (Proof.P256.combOk7 h.law) h.inv t
    spSafe := sign_spSafe (any adx h.law (Proof.P256.combOk7 h.law) h.inv t)
    features := t.features ++ (if adx then ["bmi2", "adx", "avx", "avx2"] else []).filter (!t.features.contains ·) }

def artifacts (t : Proof.Pbkdf2.Md.X86_64.Tier) (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) :
    List Artifact :=
  [withMul t h false, withMul t h true]

end VG.Generic.MdHashTier.P256.X86_64.Rfc6979
