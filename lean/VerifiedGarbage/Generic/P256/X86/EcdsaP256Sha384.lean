import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Sha384

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on x86 (32-bit)

`vg_ecdsa_p256_sha384_sign`, calling HMAC-SHA-384's `init` and `finalize`,
SHA-384's streaming `update`, and `vg_ecdsa_p256_sign`. The stack is 272
bytes: a 196-byte frame, and the 76 bytes below it that the calls use (up
to 24 bytes of arguments and the return address, and 48 bytes of stack for
HMAC's functions).

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/X86/Law.lean`.
-/

namespace VG.Generic.P256.X86.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86.Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  { Spec.Ecdsa.Rfc6979.P256Sha384.signApi with
    target := X86.target
    doc := Spec.Ecdsa.Rfc6979.P256Sha384.signApi.doc (notes := [signNotes
      Proof.Pbkdf2.Whole.X86.sha384F.hiN Proof.Pbkdf2.Whole.X86.sha384F.H.updN
      Proof.Pbkdf2.Whole.X86.sha384F.hfN 32 Spec.Ecdsa.P256.signApi.name])
    code := (cfgOf (pack h.law)).sign
    contract := Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (X86.abi.withConsts Impl.Ecdsa.X86.p256Comb.combConsts) 272
    consts := Impl.Ecdsa.X86.p256Comb.combConsts
    stack := 272
    verified := sign_verified h.law
    spSafe := sign_spSafe (pack h.law) }]

end VG.Generic.P256.X86.EcdsaP256Sha384
