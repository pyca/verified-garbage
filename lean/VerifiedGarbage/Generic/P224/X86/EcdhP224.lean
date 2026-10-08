import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P224.X86
import VerifiedGarbage.Proof.Ecdh.X86.P224.Verified
import VerifiedGarbage.Proof.Ecdh.X86.P224.Lit

/-!
# ECDH over P-224 (SP 800-56A) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/X86/Law.lean`.
-/

namespace VG.Generic.P224.X86.EcdhP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  { Spec.Ecdh.P224.exchangeApi with
    target := X86.target
    doc := Spec.Ecdh.P224.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p224_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements are eight \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`, in calls of `vg_p224_mul_mod_p` and the other \
      functions of `p224_mont`) with a final conditional subtraction. The \
      peer's key is checked without branches (its first byte, both coordinates below `p`, and \
      the curve's equation), and the ladder multiplies the peer's point if it is valid, else \
      `G`, so it always runs on a point of the curve. `[d]P` is a double-and-add ladder over all \
      256 bits of `d`, with the complete addition formulas of Renes, Costello and Batina and a \
      masked selection for each bit; `Z⁻¹` is Fermat's, by square-and-always-multiply. The \
      result (or zeros) is selected by a mask of the checks, `d` in `[1, n-1]` and `Z ≠ 0`, so \
      the time depends only on the pointers."])
    code := Impl.Ecdh.X86.exchangeP224
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst X86.abi 20
    stack := 20
    verified := Proof.Ecdh.X86.P224.ecdh_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P224.X86.EcdhP224
