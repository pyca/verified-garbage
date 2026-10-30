module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-384 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_brainpoolp384r1_sha384_sign`, calling
HMAC-SHA-384's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_brainpoolp384r1_sign`,
is emitted for every SHA-384 variant carried by `MdHash.sha384`, named with
its suffix (e.g. `vg_ecdsa_brainpoolp384r1_sha384_sign_avx2`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 240 bytes: a 216-byte frame, and the 24 bytes below it that the
calls use (`vg_ecdsa_brainpoolp384r1_sign` only its return address).

It is generic over brainpoolP384r1's group law and inversions `h` too, the variant
`Variants/BrainpoolP384r1/X86_64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.MdHash.BrainpoolP384r1.X86_64.EcdsaBrainpoolP384r1Sha384

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Sha384 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP384r1.curve) :
    List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact X86_64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv c)).sign
      stack := 240
      verified := sign_verified h.law h.inv c
      spSafe := sign_spSafe (pack h.law h.inv c)
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP384r1.X86_64.EcdsaBrainpoolP384r1Sha384
