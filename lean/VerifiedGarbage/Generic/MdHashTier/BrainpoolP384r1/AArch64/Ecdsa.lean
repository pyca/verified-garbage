module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sign
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
public import VerifiedGarbage.TCB.Emit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on AArch64, with any hash function

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_brainpoolp384r1_rfc6979_sign`, calling
HMAC's `init` and `finalize` and the streaming `update` of the hash
function its argument `hash` names (SHA-1 and the SHA-2 functions), each
the tier's implementation, and `vg_ecdsa_brainpoolp384r1_sign`, is emitted for every
tier of hash functions (`Variants/MdHashTier/AArch64/`), named with its
suffix after `hash` (e.g. `vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_sha2`), and needs
its CPU features.

The stack is 512 bytes: 16 saving `x30`, a 480-byte frame, and the 16 bytes
below it that HMAC's functions use (`vg_ecdsa_brainpoolp384r1_sign` uses none).

It is generic over brainpoolP384r1's group law `h` too, the variant
`Variants/BrainpoolP384r1/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.BrainpoolP384r1.AArch64.Ecdsa

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgT signNotes)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.Tier) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) :
    List Artifact :=
  [Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signAnyApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" [("hash", v.suffix)]
    notes := [signNotes Spec.Ecdsa.BrainpoolP384r1.signApi.name]
    code := (cfgT (Proof.Ecdsa.Rfc6979.AArch64.brainpoolp384r1 h.law h.inv) v Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.tries).sign
    stack := 512
    verified := Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sign.sign_verified v h.law h.inv
    features := v.features }]

end VG.Generic.MdHashTier.BrainpoolP384r1.AArch64.Ecdsa
