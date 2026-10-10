import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P384.Arm
import VerifiedGarbage.Proof.Ecdh.Arm.P384.Verified

/-!
# ECDH over P-384 (SP 800-56A) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/Arm/Law.lean`.
-/

namespace VG.Generic.P384.Arm.EcdhP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  { Spec.Ecdh.P384.exchangeApi with
    target := Arm.target
    doc := Spec.Ecdh.P384.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in `lr` (in `r10` \
      during the calls); field elements are twenty-four 16-bit digits in Montgomery form, multiplied by digit-by-digit \
      Montgomery multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of \
      `vg_p384_mul_mod_p` and the other functions of `p384_mont`) with a final \
      conditional subtraction. The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and the ladder multiplies the peer's \
      point if it is valid, else `G`, so it always runs on a point of the curve. `[d]P` is a \
      double-and-add ladder over all 384 bits of `d`, with the complete addition formulas of \
      Renes, Costello and Batina (calls of `vg_p384_point_double` and \
      `vg_p384_point_add`) and a masked selection for each bit; `Z⁻¹` is Fermat's, by \
      square-and-always-multiply. The result (or zeros) is selected by a mask of the checks, \
      `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.Ecdh.Arm.exchangeP384
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst Arm.abi
    verified := Proof.Ecdh.Arm.P384.ecdh_verified h.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P384.Arm.EcdhP384
