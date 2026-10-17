module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP256r1Any
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on x86-64, with the hash function as an argument

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_ecdsa_brainpoolp256r1_rfc6979_sign`, calling the tier's
`vg_hmac_init_scratch`, `vg_hash_update_scratch` and `vg_hmac_finalize_scratch`
(`Variants/MdHashTier/X86_64/`), which call the functions of the hash function
its argument `hash` names, and
`vg_ecdsa_brainpoolp256r1_sign`, is emitted for every tier, named by `Emit.qualifiedName`
(the tier's suffix, tagged `hash`), and needs the tier's CPU features. It is
generic over brainpoolP256r1's group law and inversions too, the variant
`Variants/BrainpoolP256r1/X86_64/Law.lean`.

The stack is 552 bytes: a 520-byte frame, and the 32 bytes below it that the
calls use.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.BrainpoolP256r1.X86_64.Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (sign_spSafe anyNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP256r1Any (any sign_verified)

def artifacts (t : Proof.Pbkdf2.Md.X86_64.Tier) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP256r1.curve) :
    List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signAnyApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix)]
    notes := [anyNotes 32 (Spec.Ecdsa.BrainpoolP256r1.signApi.name)]
    code := (any h.law h.inv t).code
    stack := 552
    verified := sign_verified h.law h.inv t
    spSafe := sign_spSafe (any h.law h.inv t)
    features := t.features }]

end VG.Generic.MdHashTier.BrainpoolP256r1.X86_64.Rfc6979
