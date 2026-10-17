module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_brainpoolp512r1_sha512_sign`, calling
HMAC-SHA-512's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_brainpoolp512r1_sign`,
is emitted for every SHA-512 variant carried by `MdHash.sha512`, named with
its suffix (e.g. `vg_ecdsa_brainpoolp512r1_sha512_sign_sha3`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 320 bytes: a 288-byte frame (P-384's 224 bytes, and `h` in the
64 at its top), the 16 bytes saving the link register above it, and the 16
below it that the calls use.

It is generic over brainpoolP512r1's group law and inversions `h` too, the variant
`Variants/BrainpoolP512r1/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.MdHash.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP512r1Sha512 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) :
    List Artifact :=
  match v.sha512 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact AArch64.target {
      suffix := c.suffix
      notes := [signNotes (cfgOf (pack h.law h.inv c)).H 64
          Spec.Ecdsa.BrainpoolP512r1.signApi.name 288]
      code := (cfgOf (pack h.law h.inv c)).sign
      stack := 320
      verified := sign_verified h.law h.inv c
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1Sha512
