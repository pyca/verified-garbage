import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.EcKey.P224.X86_64
import VerifiedGarbage.Proof.EcKey.X86_64.P224.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.P224.Lit

/-!
# P-224 public keys (FIPS 186-5 §A.2) on x86-64

A generic file (see `TCB/Emit.lean`) over P-224's group law and
inversions `h`, the variant
`Variants/P224/X86_64/Law.lean`.
-/

namespace VG.Generic.P224.X86_64.EcP224

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact := [
  { Spec.EcKey.P224.publicKeyApi with
    target := X86_64.target
    doc := Spec.EcKey.P224.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p224_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      its caller's callee-saved registers in `scratch`; field elements are four 64-bit words in \
      Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 256 bits of the four \
      words of `d`, with the complete addition formulas of Renes, Costello and Batina for every \
      addition and doubling and a masked selection for each bit; and `Z⁻¹` is by the signature's \
      divsteps. The result (or zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so \
      the time depends only on the pointers."])
    code := Impl.EcKey.X86_64.publicKeyP224
    contract := Spec.EcKey.P224.inst.publicKeyContract X86_64.abi
    verified := Proof.EcKey.X86_64.P224.pk_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P224.X86_64.EcP224
