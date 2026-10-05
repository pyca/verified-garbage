import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Impl.EcKey.P521.X86
import VerifiedGarbage.Proof.EcKey.X86.P521.Verified
import VerifiedGarbage.Proof.EcKey.X86.P521.Lit

/-!
# P-521 public keys (FIPS 186-5 §A.2) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/X86/Law.lean`.
-/

namespace VG.Generic.P521.X86.EcP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  { Spec.EcKey.P521.publicKeyApi with
    target := X86.target
    doc := Spec.EcKey.P521.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p521_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field \
      elements are eighteen 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 576 bits of the nine \
      words of `d`, with the complete addition formulas of Renes, Costello and Batina for every \
      addition and doubling and a masked selection for each bit; and `Z⁻¹` is Fermat's, by \
      square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.EcKey.X86.publicKeyP521
    contract := Spec.EcKey.P521.inst.publicKeyContract X86.abi
    verified := Proof.EcKey.X86.P521.pk_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P521.X86.EcP521
