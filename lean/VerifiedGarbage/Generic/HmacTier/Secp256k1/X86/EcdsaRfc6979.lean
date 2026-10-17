module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Secp256k1
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over secp256k1 on x86, with the hash function as an argument

`vg_ecdsa_secp256k1_rfc6979_sign`, calling the HMAC `init` and `finalize` and
streaming `update` of the hash function its argument `hash` names (SHA-1 and
the SHA-2 functions), of a tier (`Variants/HmacTier/X86/`), and
`vg_ecdsa_secp256k1_sign`: emitted for every tier, named with its suffix
qualified by the tag `hash` (`Emit.qualifiedName`, e.g.
`vg_ecdsa_secp256k1_rfc6979_sign_hash_shani`), and needs the tier's CPU features.

The stack is 536 bytes: a 460-byte frame, and the 76 bytes below it that the
calls use (up to 24 bytes of arguments and the return address, and 48 bytes
of stack for HMAC's functions).

It is generic over the curve's group law `h` too, the variant
`Variants/Secp256k1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.HmacTier.Secp256k1.X86.EcdsaRfc6979

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgAny anyNotes secp256k1 secp256k1_any secp256k1_spSafe)

def artifacts (t : Proof.Pbkdf2.Whole.X86.Tier) (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst.signAnyApi.artifact X86.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix)]
    notes := [anyNotes t 32 256 Spec.Ecdsa.Secp256k1.signApi.name]
    code := (cfgAny (secp256k1 h.law h.inv) t.fns Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst).sign
    stack := 536
    verified := secp256k1_any h.law h.inv t
    spSafe := secp256k1_spSafe h.law h.inv t
    features := t.features }]

end VG.Generic.HmacTier.Secp256k1.X86.EcdsaRfc6979
