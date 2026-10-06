import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P192.X86
import VerifiedGarbage.Proof.Ecdh.X86.P192.Verified
import VerifiedGarbage.Proof.Ecdh.X86.P192.Lit

/-!
# ECDH over P-192 (SP 800-56A) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-192's group law `h`, the variant
`Variants/P192/X86/Law.lean`.
-/

namespace VG.Generic.P192.X86.EcdhP192

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  { Spec.Ecdh.P192.exchangeApi with
    target := X86.target
    doc := Spec.Ecdh.P192.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p192_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements are six \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`) with a final conditional subtraction. The \
      peer's key is checked without branches (its first byte, both coordinates below `p`, and \
      the curve's equation), and the ladder multiplies the peer's point if it is valid, else \
      `G`, so it always runs on a point of the curve. `[d]P` is a double-and-add ladder over all \
      192 bits of `d`, with the complete addition formulas of Renes, Costello and Batina and a \
      masked selection for each bit; `Z⁻¹` is Fermat's, by square-and-always-multiply. The \
      result (or zeros) is selected by a mask of the checks, `d` in `[1, n-1]` and `Z ≠ 0`, so \
      the time depends only on the pointers."])
    code := Impl.Ecdh.X86.exchangeP192
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P192.inst X86.abi
    verified := Proof.Ecdh.X86.P192.ecdh_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P192.X86.EcdhP192
