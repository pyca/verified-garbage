import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521Sha512

/-!
# Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on ARMv7

`vg_ecdsa_p521_sha512_sign`, calling HMAC-SHA-512's `init` and `finalize`,
SHA-512's streaming `update`, and `vg_ecdsa_p521_sign`. The stack is 384
bytes: a 360-byte frame (P-384's 216 bytes, and 144 for the candidate and
the digest shifted into 66 bytes), and the 24 bytes below it that the calls
use (a call's 8 or 16 bytes of stack arguments, and the stack of the
function it calls below them).

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/Arm/Law.lean`.
-/

namespace VG.Generic.P521.Arm.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf signNotesWide)
open VG.Proof.Ecdsa.Rfc6979.Arm.P521Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  { Spec.Ecdsa.Rfc6979.P521Sha512.signApi with
    target := Arm.target
    doc := Spec.Ecdsa.Rfc6979.P521Sha512.signApi.doc (notes := [signNotesWide
      Proof.Pbkdf2.Whole.Arm.sha512F.hiN Proof.Pbkdf2.Whole.Arm.sha512F.H.updN
      Proof.Pbkdf2.Whole.Arm.sha512F.hfN 66 521 64 Spec.Ecdsa.P521.signApi.name])
    code := (cfgOf (pack h.law)).sign
    contract := Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract Arm.abi 384
    stack := 384
    verified := sign_verified h.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P521.Arm.EcdsaP521Sha512
