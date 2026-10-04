import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Sha384

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on x86 (32-bit)

`vg_ecdsa_p256_sha384_sign`, calling HMAC-SHA-384's `init` and `finalize`,
SHA-384's streaming `update`, and `vg_ecdsa_p256_sign`. The stack is 256
bytes: a 180-byte frame, and the 76 bytes below it that the calls use (up
to 24 bytes of arguments and the return address, and 48 bytes of stack for
HMAC's functions).
-/

namespace VG.Artifacts.EcdsaP256Sha384.X86

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86.Sha384 (pack sign_verified)

def artifacts : List Artifact := [
  { Spec.Ecdsa.Rfc6979.P256Sha384.signApi with
    target := X86.target
    doc := Spec.Ecdsa.Rfc6979.P256Sha384.signApi.doc (notes := [signNotes
      Proof.Pbkdf2.Whole.X86.sha384F.hiN Proof.Pbkdf2.Whole.X86.sha384F.H.updN
      Proof.Pbkdf2.Whole.X86.sha384F.hfN])
    code := (cfgOf (pack Proof.P256.law)).sign
    contract := Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract X86.abi 256
    stack := 256
    verified := sign_verified Proof.P256.law
    spSafe := sign_spSafe (pack Proof.P256.law) }]

end VG.Artifacts.EcdsaP256Sha384.X86
