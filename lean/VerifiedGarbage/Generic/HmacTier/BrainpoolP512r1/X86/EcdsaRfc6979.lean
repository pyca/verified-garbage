module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP512r1
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP512r1 on x86, with the hash function as an argument

`vg_ecdsa_brainpoolp512r1_rfc6979_sign`, calling the HMAC `init` and `finalize` and
streaming `update` of the hash function its argument `hash` names (SHA-1 and
the SHA-2 functions), of a tier (`Variants/HmacTier/X86/`), and
`vg_ecdsa_brainpoolp512r1_sign`: emitted for every tier, named with its suffix
qualified by the tag `hash` (`Emit.qualifiedName`, e.g.
`vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani`), and needs the tier's CPU features.

The stack is 536 bytes: a 460-byte frame, and the 76 bytes below it that the
calls use (up to 24 bytes of arguments and the return address, and 48 bytes
of stack for HMAC's functions).

It is generic over the curve's group law `h` too, the variant
`Variants/BrainpoolP512r1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.HmacTier.BrainpoolP512r1.X86.EcdsaRfc6979

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgAny anyNotes brainpoolp512r1 brainpoolp512r1_any brainpoolp512r1_spSafe)

def artifacts (t : Proof.Pbkdf2.Whole.X86.Tier) (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signAnyApi.artifact X86.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix)]
    notes := [anyNotes t 64 512 Spec.Ecdsa.BrainpoolP512r1.signApi.name]
    code := (cfgAny (brainpoolp512r1 h.law) t.fns Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst).sign
    stack := 536
    verified := brainpoolp512r1_any h.law t
    spSafe := brainpoolp512r1_spSafe h.law t
    features := t.features }]

end VG.Generic.HmacTier.BrainpoolP512r1.X86.EcdsaRfc6979
