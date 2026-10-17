module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224Any
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-224 on x86-64, with the hash function as an argument

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_ecdsa_p224_rfc6979_sign`, calling HMAC's `init` and `finalize` and the
streaming `update` of the hash function its argument `hash` names, each of
the tier's implementation (`Variants/MdHashTier/X86_64/`), and
`vg_ecdsa_p224_sign`, is emitted for every tier, named by `Emit.qualifiedName`
(the tier's suffix, tagged `hash`), and needs the tier's CPU features. It is
generic over P-224's group law and inversions too, the variant
`Variants/P224/X86_64/Law.lean`.

The stack is 544 bytes: a 520-byte frame, and the 24 bytes below it that the
calls use.

It reads the comb's tables of `vg_ecdsa_p224_sign`, the static `VG_P224_COMB`.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.P224.X86_64.Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (sign_spSafe anyNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P224Any (any sign_verified)

def artifacts (t : Proof.Pbkdf2.Md.X86_64.Tier) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) :
    List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.inst.signAnyApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix)]
    notes := [anyNotes 28 (Spec.Ecdsa.P224.signApi.name)]
    code := (any h.law (Proof.P224.combOk7 h.law) h.inv t).code
    consts := Impl.Ecdsa.X86_64.p224.combConsts
    stack := 544
    verified := sign_verified h.law (Proof.P224.combOk7 h.law) h.inv t
    spSafe := sign_spSafe (any h.law (Proof.P224.combOk7 h.law) h.inv t)
    features := t.features }]

end VG.Generic.MdHashTier.P224.X86_64.Rfc6979
