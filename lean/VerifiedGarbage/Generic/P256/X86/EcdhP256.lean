import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P256.X86
import VerifiedGarbage.Proof.Ecdh.X86.Verified
import VerifiedGarbage.Proof.Ecdh.X86.Lit

/-!
# ECDH over P-256 (SP 800-56A) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/X86/Law.lean`.
-/

namespace VG.Generic.P256.X86.EcdhP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  { Spec.Ecdh.P256.exchangeApi with
    target := X86.target
    doc := Spec.Ecdh.P256.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s setup, \
      field arithmetic and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements are eight \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`) with a final conditional subtraction. The \
      peer's key is checked without branches (its first byte, both coordinates below `p`, and \
      the curve's equation), and the window method multiplies the peer's point if it is valid, else \
      `G`, so it always runs on a point of the curve. `[d]P` uses 65 signed four-bit windows, \
      with Jacobian doublings, complete additions, and constant-time scans of eight projective \
      points; `Z⁻¹` uses a fixed chain for `p - 2` (255 squares and 18 other multiplications). The \
      result (or zeros) is selected by a mask of the checks, `d` in `[1, n-1]` and `Z ≠ 0`, so \
      the time depends only on the pointers."])
    code := Impl.Ecdh.X86.exchangeP256
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86.abi
    verified := Proof.Ecdh.X86.ecdh_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P256.X86.EcdhP256
