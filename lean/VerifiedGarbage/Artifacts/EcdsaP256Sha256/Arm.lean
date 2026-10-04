import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Sha256

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-256 on ARMv7

`vg_ecdsa_p256_sha256_sign`, calling HMAC-SHA-256's `init` and `finalize`,
SHA-256's streaming `update`, and `vg_ecdsa_p256_sign`. The stack is 224
bytes: a 200-byte frame, and the 24 bytes below it that the calls use (a
call's 8 or 16 bytes of stack arguments, and the stack of the function it
calls below them).
-/

namespace VG.Artifacts.EcdsaP256Sha256.Arm

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.Arm.Sha256 (pack sign_verified)

def artifacts : List Artifact := [
  { Spec.Ecdsa.Rfc6979.P256Sha256.signApi with
    target := Arm.target
    doc := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.doc (notes := [signNotes
      Proof.Pbkdf2.Whole.Arm.sha256F.hiN Proof.Pbkdf2.Whole.Arm.sha256F.H.updN
      Proof.Pbkdf2.Whole.Arm.sha256F.hfN])
    code := (cfgOf (pack Proof.P256.law)).sign
    contract := Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract Arm.abi 224
    stack := 224
    verified := sign_verified Proof.P256.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcdsaP256Sha256.Arm
