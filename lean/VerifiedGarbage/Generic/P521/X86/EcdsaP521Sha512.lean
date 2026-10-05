import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P521Sha512

/-!
# Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on x86 (32-bit)

`vg_ecdsa_p521_sha512_sign`, calling HMAC-SHA-512's `init` and `finalize`,
SHA-512's streaming `update`, and `vg_ecdsa_p521_sign`. The stack is 416
bytes: a 340-byte frame (P-384's 196 bytes, and 144 for the candidate and
the digest shifted into 66 bytes), and the 76 bytes below it that the calls
use (up to 24 bytes of arguments and the return address, and 48 bytes of
stack for HMAC's functions).

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/X86/Law.lean`.
-/

namespace VG.Generic.P521.X86.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe signNotesWide)
open VG.Proof.Ecdsa.Rfc6979.X86.P521Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  { Spec.Ecdsa.Rfc6979.P521Sha512.signApi with
    target := X86.target
    doc := Spec.Ecdsa.Rfc6979.P521Sha512.signApi.doc (notes := [signNotesWide
      Proof.Pbkdf2.Whole.X86.sha512F.hiN Proof.Pbkdf2.Whole.X86.sha512F.H.updN
      Proof.Pbkdf2.Whole.X86.sha512F.hfN 66 521 64 Spec.Ecdsa.P521.signApi.name])
    code := (cfgOf (pack h.law)).sign
    contract := Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract X86.abi 416
    stack := 416
    verified := sign_verified h.law
    spSafe := sign_spSafe (pack h.law) }]

end VG.Generic.P521.X86.EcdsaP521Sha512
