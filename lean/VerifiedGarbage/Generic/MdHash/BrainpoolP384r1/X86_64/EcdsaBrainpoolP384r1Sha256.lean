module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Sha256
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-256 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_brainpoolp384r1_sha256_sign`, calling
HMAC-SHA-256's `init` and `finalize` and SHA-256's streaming `update` made
with the variant's SHA-256 compression function, and `vg_ecdsa_brainpoolp384r1_sign`,
is emitted for every SHA-256 variant carried by `MdHash.sha256`, named with
its suffix (e.g. `vg_ecdsa_brainpoolp384r1_sha256_sign_shani`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 240 bytes: a 216-byte frame, and the 24 bytes below it that the
calls use (`vg_ecdsa_brainpoolp384r1_sign` only its return address).

It is generic over brainpoolP384r1's group law and inversions `h` too, the variant
`Variants/BrainpoolP384r1/X86_64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.MdHash.BrainpoolP384r1.X86_64.EcdsaBrainpoolP384r1Sha256

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Sha256 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP384r1.curve) :
    List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha256.signApi with
      name := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha256.signApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha256.signApi.doc
        (notes := [signNotes (cfgOf (pack h.law h.inv c)).H 32
          Spec.Ecdsa.BrainpoolP384r1.signApi.name])
      code := (cfgOf (pack h.law h.inv c)).sign
      contract := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha256.inst.signContract
        X86_64.abi 240
      stack := 240
      verified := sign_verified h.law h.inv c
      spSafe := sign_spSafe (pack h.law h.inv c)
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP384r1.X86_64.EcdsaBrainpoolP384r1Sha256
