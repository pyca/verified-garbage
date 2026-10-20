module

public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224Sha224
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified

/-!
# Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p224_sha224_sign`, calling
HMAC-SHA-224's `init` and `finalize` and SHA-256's streaming `update` made
with the variant's SHA-256 compression function, and `vg_ecdsa_p224_sign`,
is emitted for every SHA-224 variant carried by `MdHash.sha224`, named with
its suffix (e.g. `vg_ecdsa_p224_sha224_sign_shani`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 240 bytes: a 216-byte frame, and the 24 bytes below it that the
calls use (`vg_ecdsa_p224_sign` only its return address).

It reads the comb's tables of `vg_ecdsa_p224_sign`, the static `VG_P224_COMB`.
It is generic over P-224's group law and inversions `h` too, the variant
`Variants/P224/X86_64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.MdHash.P224.X86_64.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P224Sha224 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) :
    List Artifact :=
  match v.sha224 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact X86_64.target {
      suffix := c.suffix
      notes := [signNotes (cfgOf (pack h.law (Proof.P224.combOk7 h.law) h.inv c)).H 28
          Spec.Ecdsa.P224.signApi.name]
      code := (cfgOf (pack h.law (Proof.P224.combOk7 h.law) h.inv c)).sign
      consts := Impl.Ecdsa.X86_64.p224.combConsts
      stack := 240
      verified := sign_verified h.law (Proof.P224.combOk7 h.law) h.inv c
      spSafe := sign_spSafe (pack h.law (Proof.P224.combOk7 h.law) h.inv c)
      features := c.features }]

end VG.Generic.MdHash.P224.X86_64.EcdsaP224Sha224
