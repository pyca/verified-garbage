module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_brainpoolp512r1_sha512_sign`, calling
HMAC-SHA-512's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_brainpoolp512r1_sign`,
is emitted for every SHA-512 variant carried by `MdHash.sha512`, named with
its suffix (e.g. `vg_ecdsa_brainpoolp512r1_sha512_sign_avx2`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 304 bytes: a 280-byte frame (P-384's 216 bytes, and `h` in the
64 above its pointers), and the 24 bytes below it that the
calls use (`vg_ecdsa_brainpoolp512r1_sign` only its return address).

It is generic over brainpoolP512r1's group law and inversions `h` too, the variant
`Variants/BrainpoolP512r1/X86_64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.MdHash.BrainpoolP512r1.X86_64.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP512r1Sha512 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP512r1.curve) :
    List Artifact :=
  match v.sha512 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact X86_64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv c)).sign
      stack := 304
      verified := sign_verified h.law h.inv c
      spSafe := sign_spSafe (pack h.law h.inv c)
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP512r1.X86_64.EcdsaBrainpoolP512r1Sha512
