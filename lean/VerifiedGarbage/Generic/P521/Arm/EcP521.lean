import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.EcKey.P521.Arm
import VerifiedGarbage.Proof.EcKey.Arm.P521.Verified

/-!
# P-521 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/Arm/Law.lean`.
-/

namespace VG.Generic.P521.Arm.EcP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  { Spec.EcKey.P521.publicKeyApi with
    target := Arm.target
    doc := Spec.EcKey.P521.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p521_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in \
      `lr`; field elements are thirty-six 16-bit digits in Montgomery form, multiplied by \
      digit-by-digit Montgomery multiplication (CIOS, with `mul` and the accumulator in \
      `scratch`) with a final conditional subtraction; `[d]G` is a double-and-add ladder over \
      all 576 bits of the nine words of `d`, with the complete addition formulas of Renes, \
      Costello and Batina for every addition and doubling and a masked selection for each bit; \
      and `Z⁻¹` is Fermat's, by square-and-always-multiply over the bits of `p - 2`. The result \
      (or zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only \
      on the pointers."])
    code := Impl.EcKey.Arm.publicKeyP521
    contract := Spec.EcKey.P521.inst.publicKeyContract Arm.abi
    verified := Proof.EcKey.Arm.P521.pk_verified h.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P521.Arm.EcP521
