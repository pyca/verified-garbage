module

public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P224Sha224
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p224_sha224_sign`, calling
HMAC-SHA-224's `init` and `finalize` and SHA-256's streaming `update` made
with the variant's SHA-256 compression function, and `vg_ecdsa_p224_sign`,
is emitted for every SHA-224 variant carried by `MdHash.sha224`, named with
its suffix (e.g. `vg_ecdsa_p224_sha224_sign_sha2`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 256 bytes: 16 saving `x30`, a 224-byte frame, and the 16 bytes
below it that HMAC's functions use (`vg_ecdsa_p224_sign` uses none).

It is generic over P-224's group law and inversions `h` too, the variant
`Variants/P224/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.MdHash.P224.AArch64.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.AArch64.P224Sha224 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) :
    List Artifact :=
  match v.sha224 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact AArch64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv (Proof.P224.combOk7 h.law) c)).sign
      consts := Impl.Ecdsa.AArch64.p224.combConsts
      stack := 256
      verified := sign_verified h.law h.inv (Proof.P224.combOk7 h.law) c
      features := c.features }]

end VG.Generic.MdHash.P224.AArch64.EcdsaP224Sha224
