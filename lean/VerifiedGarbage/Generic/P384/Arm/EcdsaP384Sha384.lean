import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384Sha384

/-!
# Deterministic ECDSA (RFC 6979) over P-384 with HMAC-SHA-384 on ARMv7

`vg_ecdsa_p384_sha384_sign`, calling HMAC-SHA-384's `init` and `finalize`,
SHA-384's streaming `update`, and `vg_ecdsa_p384_sign`. The stack is 240
bytes: a 216-byte frame, and the 24 bytes below it that the calls use (a
call's 8 or 16 bytes of stack arguments, and the stack of the function it
calls below them).

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/Arm/Law.lean`.
-/

namespace VG.Generic.P384.Arm.EcdsaP384Sha384

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.Arm.P384Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  { Spec.Ecdsa.Rfc6979.P384Sha384.signApi with
    target := Arm.target
    doc := Spec.Ecdsa.Rfc6979.P384Sha384.signApi.doc (notes := [signNotes
      Proof.Pbkdf2.Whole.Arm.sha384F.hiN Proof.Pbkdf2.Whole.Arm.sha384F.H.updN
      Proof.Pbkdf2.Whole.Arm.sha384F.hfN 48 Spec.Ecdsa.P384.signApi.name])
    code := (cfgOf (pack h.law)).sign
    contract := Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract Arm.abi 240
    stack := 240
    verified := sign_verified h.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P384.Arm.EcdsaP384Sha384
