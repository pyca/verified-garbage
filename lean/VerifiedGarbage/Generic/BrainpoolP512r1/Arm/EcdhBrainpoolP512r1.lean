module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# ECDH over brainpoolP512r1 (SP 800-56A) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.Arm.EcdhBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  { Spec.Ecdh.BrainpoolP512r1.exchangeApi with
    target := Arm.target
    doc := Spec.Ecdh.BrainpoolP512r1.exchangeApi.doc (notes := ["The function uses the generic Weierstrass setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in `lr` (in `r10` \
      during the calls); field elements are thirty-two 16-bit digits in Montgomery form, multiplied by digit-by-digit \
      Montgomery multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of \
      `vg_brainpoolp512r1_mul_mod_p` and the other functions of `brainpoolp512r1_mont`) with a final \
      conditional subtraction. The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and the ladder multiplies the peer's \
      point if it is valid, else `G`, so it always runs on a point of the curve. `[d]P` is a \
      double-and-add ladder over all 512 bits of `d`, with the complete addition formulas of \
      Renes, Costello and Batina (inlined for eight-word coordinates) and a masked selection for each bit; `Z⁻¹` is Fermat's, by \
      square-and-always-multiply. The result (or zeros) is selected by a mask of the checks, \
      `d` in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.Ecdh.Arm.exchangeBrainpoolP512r1
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst Arm.abi
    verified := Proof.Ecdh.Arm.BrainpoolP512r1.ecdh_verified h.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.BrainpoolP512r1.Arm.EcdhBrainpoolP512r1
