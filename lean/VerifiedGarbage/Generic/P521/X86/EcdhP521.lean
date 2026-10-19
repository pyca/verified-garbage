module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P521.X86
public import VerifiedGarbage.Proof.Ecdh.X86.P521.Verified
import VerifiedGarbage.Proof.Ecdh.X86.P521.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P521

/-!
# ECDH over P-521 (SP 800-56A) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.X86.EcdhP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact X86.target {
    notes := ["The function is `vg_ecdsa_p521_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements are eighteen \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`, in calls of `vg_p521_mul_mod_p` and the other \
      functions of `p521_mont`) with a final conditional subtraction. The \
      peer's key is checked without branches (its first byte, both coordinates below `p`, and \
      the curve's equation), and the ladder multiplies the peer's point if it is valid, else \
      `G`, so it always runs on a point of the curve. `[d]P` is a double-and-add ladder over all \
      576 bits of the nine words of `d`, with the complete addition formulas of Renes, Costello \
      and Batina and a masked selection for each bit; `Z⁻¹` is Fermat's, by square-and-always-multiply. The \
      result (or zeros) is selected by a mask of the checks, `d` in `[1, n-1]` and `Z ≠ 0`, so \
      the time depends only on the pointers."]
    code := Impl.Ecdh.X86.exchangeP521
    stack := 20
    verified := Proof.Ecdh.X86.P521.ecdh_verified h.law }]

end VG.Generic.P521.X86.EcdhP521
