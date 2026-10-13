module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sha384
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

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
    { Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi with
      name := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.name ++ c.suffix
      target := AArch64.target
      doc := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.doc
        (notes := [signNotes (cfgOf (pack h.law h.inv c)).H 48
          Spec.Ecdsa.BrainpoolP384r1.signApi.name])
      code := (cfgOf (pack h.law h.inv c)).sign
      contract := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signContract
        AArch64.abi 256
      stack := 256
      verified := sign_verified h.law h.inv c
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP384r1.AArch64.EcdsaBrainpoolP384r1Sha384
