import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.P384.Curve
import VerifiedGarbage.Impl.EcKey.P384.X86_64
import VerifiedGarbage.Proof.EcKey.X86_64.P384.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.P384.Lit

/-! # P-384 public keys (FIPS 186-5 §A.2) on x86-64 -/

namespace VG.Artifacts.EcP384.X86_64

def artifacts : List Artifact := [
  { Spec.EcKey.P384.publicKeyApi with
    target := X86_64.target
    doc := Spec.EcKey.P384.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves its caller's callee-saved registers in `scratch`; field elements are six 64-bit \
      words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS) \
      with a final conditional subtraction; `[d]G` is a double-and-add ladder over all 384 \
      bits of `d`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling and a masked selection for each bit; and `Z⁻¹` is Fermat's, \
      by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is \
      selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the \
      pointers."])
    code := Impl.EcKey.X86_64.publicKeyP384
    contract := Spec.EcKey.P384.inst.publicKeyContract X86_64.abi
    verified := Proof.EcKey.X86_64.P384.pk_verified Proof.P384.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.EcP384.X86_64
