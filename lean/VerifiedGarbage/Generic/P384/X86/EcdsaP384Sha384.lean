import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P384Sha384

/-!
# Deterministic ECDSA (RFC 6979) over P-384 with HMAC-SHA-384 on x86 (32-bit)

`vg_ecdsa_p384_sha384_sign`, calling HMAC-SHA-384's `init` and `finalize`,
SHA-384's streaming `update`, and `vg_ecdsa_p384_sign`. The stack is 272
bytes: a 196-byte frame, and the 76 bytes below it that the calls use (up
to 24 bytes of arguments and the return address, and 48 bytes of stack for
HMAC's functions).

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/X86/Law.lean`.
-/

namespace VG.Generic.P384.X86.EcdsaP384Sha384

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86.P384Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  { Spec.Ecdsa.Rfc6979.P384Sha384.signApi with
    target := X86.target
    doc := Spec.Ecdsa.Rfc6979.P384Sha384.signApi.doc (notes := [signNotes
      Proof.Pbkdf2.Whole.X86.sha384F.hiN Proof.Pbkdf2.Whole.X86.sha384F.H.updN
      Proof.Pbkdf2.Whole.X86.sha384F.hfN 48 Spec.Ecdsa.P384.signApi.name])
    code := (cfgOf (pack h.law)).sign
    contract := Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract X86.abi 272
    stack := 272
    verified := sign_verified h.law
    spSafe := sign_spSafe (pack h.law) }]

end VG.Generic.P384.X86.EcdsaP384Sha384
