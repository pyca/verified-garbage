module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.Arm
import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1

/-!
# brainpoolP512r1 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.Arm.EcBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact Arm.target {
    notes := ["The function uses the generic Weierstrass ladder and inversion of `Z`: it \
      saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in \
      `lr` (in `r10` during the calls); field elements are thirty-two 16-bit digits in Montgomery form, multiplied by \
      digit-by-digit Montgomery multiplication (CIOS, with `mul` and the accumulator in \
      `scratch`, in calls of `vg_brainpoolp512r1_mul_mod_p` and the other functions of `brainpoolp512r1_mont`) \
      with a final conditional subtraction; `[d]G` is a double-and-add ladder over \
      all 512 bits of `d`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling (inlined for eight-word coordinates) and a masked selection for each bit; and `Z⁻¹` is Fermat's, \
      by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.Arm.publicKeyBrainpoolP512r1
    verified := Proof.EcKey.Arm.BrainpoolP512r1.pk_verified h.law }]

end VG.Generic.BrainpoolP512r1.Arm.EcBrainpoolP512r1
