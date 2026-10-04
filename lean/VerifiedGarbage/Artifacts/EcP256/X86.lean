import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Impl.EcKey.P256.X86
import VerifiedGarbage.Proof.EcKey.X86.Verified
import VerifiedGarbage.Proof.EcKey.X86.Lit

/-! # P-256 public keys (FIPS 186-5 §A.2) on x86 (32-bit) -/

namespace VG.Artifacts.EcP256.X86

def artifacts : List Artifact := [
  { Spec.EcKey.P256.publicKeyApi with
    target := X86.target
    doc := Spec.EcKey.P256.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field \
      elements are eight 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 256 bits of `d`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling and a masked selection for each bit; and `Z⁻¹` is Fermat's, by \
      square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.EcKey.X86.publicKeyP256
    contract := Spec.EcKey.P256.inst.publicKeyContract X86.abi
    verified := Proof.EcKey.X86.pk_verified Proof.P256.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.EcP256.X86
