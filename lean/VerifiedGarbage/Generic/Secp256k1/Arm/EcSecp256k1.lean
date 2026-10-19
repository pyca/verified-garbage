module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Secp256k1.Arm
import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.Verified
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.Secp256k1

/-!
# secp256k1 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    notes := ["The function is `vg_ecdsa_secp256k1_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in \
      `lr` (in `r10` during the calls); field elements are sixteen 16-bit digits in Montgomery \
      form, multiplied by \
      digit-by-digit Montgomery multiplication (CIOS, with `mul` and the accumulator in \
      `scratch`, in calls of `vg_secp256k1_mul_mod_p` and the other functions of `secp256k1_mont`) \
      with a final conditional subtraction; `[d]G` is a double-and-add ladder over \
      all 256 bits of `d`, with the complete addition formulas of Renes, Costello and Batina for \
      every addition and doubling (calls of `vg_secp256k1_point_double` and \
      `vg_secp256k1_point_add`) and a masked selection for each bit; and `Z⁻¹` is Fermat's, \
      by square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.Arm.publicKeySecp256k1
    verified := Proof.EcKey.Arm.Secp256k1.pk_verified h.law }]

end VG.Generic.Secp256k1.Arm.EcSecp256k1
