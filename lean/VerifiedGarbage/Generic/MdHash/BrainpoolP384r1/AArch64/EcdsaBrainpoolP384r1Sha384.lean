module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-384 on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_brainpoolp384r1_sha384_sign`, calling
HMAC-SHA-384's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_brainpoolp384r1_sign`,
is emitted for every SHA-384 variant carried by `MdHash.sha384`, named with
its suffix (e.g. `vg_ecdsa_brainpoolp384r1_sha384_sign_sha3`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 256 bytes, including the saved link register and nested calls.

It is generic over brainpoolP384r1's group law and inversions `h` too, the variant
`Variants/BrainpoolP384r1/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.MdHash.BrainpoolP384r1.AArch64.EcdsaBrainpoolP384r1Sha384

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sha384 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) :
    List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact AArch64.target {
      suffix := c.suffix
      notes := [signNotes (cfgOf (pack h.law h.inv c)).H 48
          Spec.Ecdsa.BrainpoolP384r1.signApi.name]
      code := (cfgOf (pack h.law h.inv c)).sign
      stack := 256
      verified := sign_verified h.law h.inv c
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP384r1.AArch64.EcdsaBrainpoolP384r1Sha384
