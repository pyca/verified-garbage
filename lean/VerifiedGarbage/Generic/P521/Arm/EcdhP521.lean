import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P521.Arm
import VerifiedGarbage.Proof.Ecdh.Arm.P521.Verified

/-!
# ECDH over P-521 (SP 800-56A) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/Arm/Law.lean`.
-/

namespace VG.Generic.P521.Arm.EcdhP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  { Spec.Ecdh.P521.exchangeApi with
    target := Arm.target
    doc := Spec.Ecdh.P521.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p521_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in `lr`; field \
      elements are thirty-six 16-bit digits in Montgomery form, multiplied by digit-by-digit \
      Montgomery multiplication (CIOS, with `mul` and the accumulator in `scratch`) with a final \
      conditional subtraction. The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and the ladder multiplies the peer's \
      point if it is valid, else `G`, so it always runs on a point of the curve. `[d]P` is a \
      double-and-add ladder over all 576 bits of the nine words of `d`, with the complete \
      addition formulas of Renes, Costello and Batina and a masked selection for each bit; \
      `Z⁻¹` is Fermat's, by \
      square-and-always-multiply. The result (or zeros) is selected by a mask of the checks, \
      `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.Ecdh.Arm.exchangeP521
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst Arm.abi
    verified := Proof.Ecdh.Arm.P521.ecdh_verified h.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P521.Arm.EcdhP521
