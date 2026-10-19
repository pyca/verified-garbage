module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.Arm
import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1

/-!
# brainpoolP256r1 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law `h`, the variant
`Variants/BrainpoolP256r1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target {
    notes := ["The function is `vg_ecdsa_brainpoolp256r1_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in \
      `lr` (in `r10` during the calls); field elements are sixteen 16-bit digits in Montgomery \
      form, multiplied by \
      digit-by-digit Montgomery multiplication (CIOS, with `mul` and the accumulator in \
      `scratch`, in calls of `vg_brainpoolp256r1_mul_mod_p` and the other functions of `brainpoolp256r1_mont`) \
      with a final conditional subtraction; `[d]G` is a double-and-add ladder over \
      all 256 bits of `d`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling (calls of `vg_brainpoolp256r1_point_double` and \
      `vg_brainpoolp256r1_point_add`) and a masked selection for each bit; and `Z⁻¹` is Fermat's, \
      by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.Arm.publicKeyBrainpoolP256r1
    verified := Proof.EcKey.Arm.BrainpoolP256r1.pk_verified h.law }]

end VG.Generic.BrainpoolP256r1.Arm.EcBrainpoolP256r1
