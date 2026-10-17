module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384Any
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-384 on x86-64, with the hash function as an argument

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_ecdsa_p384_rfc6979_sign`, calling the tier's
`vg_hmac_init_scratch`, `vg_hash_update_scratch` and `vg_hmac_finalize_scratch`
(`Variants/MdHashTier/X86_64/`), which call the functions of the hash function
its argument `hash` names, and
`vg_ecdsa_p384_sign`, is emitted for every tier, named by `Emit.qualifiedName`
(the tier's suffix, tagged `hash`), and needs the tier's CPU features. It is
generic over P-384's group law and inversions too, the variant
`Variants/P384/X86_64/Law.lean`. It is emitted for each multiplication of
`vg_ecdsa_p384_sign`: the baseline's, and BMI2's and ADX's (`vg_ecdsa_p384_sign_adx`,
which the instances with the suffix `_adx` call).

The stack is 552 bytes: a 520-byte frame, and the 32 bytes below it that the
calls use.

It reads the comb's tables of `vg_ecdsa_p384_sign`, the static `VG_P384_COMB`.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.P384.X86_64.Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (sign_spSafe anyNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P384Any (any sign_verified)

/-- The signature with the tier `t`, and P-384's multiplication with BMI2 and
ADX (`adx`, `_adx`, calling `vg_ecdsa_p384_sign_adx`) or not. -/
def withMul (t : Proof.Pbkdf2.Md.X86_64.Tier) (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve)
    (adx : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.P384Sha384.inst.signAnyApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix)] ++ (if adx then "_adx" else "")
    notes := [anyNotes 48 (Spec.Ecdsa.P384.signApi.name ++ (if adx then "_adx" else ""))]
    code := (any adx h.law (Proof.P384.combOk7 h.law) h.inv t).code
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    stack := 552
    verified := sign_verified adx h.law (Proof.P384.combOk7 h.law) h.inv t
    spSafe := sign_spSafe (any adx h.law (Proof.P384.combOk7 h.law) h.inv t)
    features := t.features ++ (if adx then ["bmi2", "adx", "avx", "avx2"] else []).filter (!t.features.contains ·) }

def artifacts (t : Proof.Pbkdf2.Md.X86_64.Tier) (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) :
    List Artifact :=
  [withMul t h false, withMul t h true]

end VG.Generic.MdHashTier.P384.X86_64.Rfc6979
