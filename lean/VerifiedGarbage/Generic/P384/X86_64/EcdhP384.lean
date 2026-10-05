import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P384.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Lit

/-!
# ECDH over P-384 (SP 800-56A) on x86-64

A generic file (see `TCB/Emit.lean`) over P-384's group law and
inversions `h`, the variant `Variants/P384/X86_64/Law.lean`.
-/

namespace VG.Generic.P384.X86_64.EcdhP384

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P384.curve) : List Artifact := [
  { Spec.Ecdh.P384.exchangeApi with
    target := X86_64.target
    doc := Spec.Ecdh.P384.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves its \
      caller's callee-saved registers in `scratch`; field elements are six 64-bit words in \
      Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final \
      conditional subtraction. The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and the ladder multiplies the peer's \
      point if it is valid, else `G`, so it always runs on a point of the curve. `[d]P` is a \
      double-and-add ladder over all 384 bits of `d`, with the complete addition formulas of \
      Renes, Costello and Batina and a masked selection for each bit; `Z⁻¹` is by the \
      signature's divsteps. The result (or zeros) is selected by a mask of the checks, `d` \
      in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.Ecdh.X86_64.exchangeP384
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst X86_64.abi
    verified := Proof.Ecdh.X86_64.P384.ecdh_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P384.X86_64.EcdhP384
