import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.EcKey.P224.X86
import VerifiedGarbage.Proof.EcKey.X86.P224.Verified
import VerifiedGarbage.Proof.EcKey.X86.P224.Lit

/-!
# P-224 public keys (FIPS 186-5 §A.2) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/X86/Law.lean`.
-/

namespace VG.Generic.P224.X86.EcP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  { Spec.EcKey.P224.publicKeyApi with
    target := X86.target
    doc := Spec.EcKey.P224.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p224_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field \
      elements are eight 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of `vg_p224_mul_mod_p` and the other \
      functions of `p224_mont`) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 256 bits of `d`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling and a masked selection for each bit; and `Z⁻¹` is Fermat's, by \
      square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.EcKey.X86.publicKeyP224
    contract := Spec.EcKey.P224.inst.publicKeyContract X86.abi 20
    stack := 20
    verified := Proof.EcKey.X86.P224.pk_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P224.X86.EcP224
