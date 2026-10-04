import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Impl.Ecdsa.P256.Arm
import VerifiedGarbage.Proof.Ecdsa.Arm.Verified

/-! # ECDSA over P-256 (FIPS 186-5) on 32-bit ARM -/

namespace VG.Artifacts.EcdsaP256.Arm

def artifacts : List Artifact := [
  { Spec.Ecdsa.P256.signApi with
    target := Arm.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves the callee-saved registers \
      `r4`–`r11` and `lr` in `scratch`, and keeps `out` in `lr`. Field elements and scalars are \
      sixteen 16-bit digits in Montgomery form, multiplied by digit-by-digit Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`) with a final \
      conditional subtraction. `[k]G` is a double-and-add ladder over all 256 bits of `k`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling and a masked selection for each bit; the inversions modulo `p` and `n` are \
      Fermat's, by square-and-always-multiply over the bits of `p - 2` and `n - 2`. The \
      signature (or zeros) is selected by a mask, so the time depends only on the pointers."])
    code := Impl.Ecdsa.Arm.signP256
    contract := Spec.Ecdsa.P256.inst.signContract Arm.abi
    verified := Proof.Ecdsa.Arm.sign_verified Proof.P256.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcdsaP256.Arm
