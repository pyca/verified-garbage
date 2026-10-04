import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Impl.EcKey.P256.Arm
import VerifiedGarbage.Proof.EcKey.Arm.Verified

/-! # P-256 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

namespace VG.Artifacts.EcP256.Arm

def artifacts : List Artifact := [
  { Spec.EcKey.P256.publicKeyApi with
    target := Arm.target
    doc := Spec.EcKey.P256.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in \
      `lr`; field elements are sixteen 16-bit digits in Montgomery form, multiplied by \
      digit-by-digit Montgomery multiplication (CIOS, with `mul` and the accumulator in \
      `scratch`) with a final conditional subtraction; `[d]G` is a double-and-add ladder over \
      all 256 bits of `d`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling and a masked selection for each bit; and `Z⁻¹` is Fermat's, \
      by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.EcKey.Arm.publicKeyP256
    contract := Spec.EcKey.P256.inst.publicKeyContract Arm.abi
    verified := Proof.EcKey.Arm.pk_verified Proof.P256.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcP256.Arm
