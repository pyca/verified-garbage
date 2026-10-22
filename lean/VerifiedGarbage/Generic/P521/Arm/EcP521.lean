module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.P521.Arm
import VerifiedGarbage.Proof.EcKey.Arm.P521.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Proof.EcKey.Arm.P521.Verified
import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.EcKey.Arm.Finish
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
public import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
public import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
public import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Rc2.Select
public import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
public import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
public import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
public import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.X25519.Arm.Limbs
public import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.EcKey.Arm.Finish
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.X25519.Arm.Limbs
import VerifiedGarbage.Proof.X25519.Field

/-!
# P-521 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.Arm.EcP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.EcKey.P521.publicKeyApi.artifact Arm.target {
    notes := ["The function is `vg_ecdsa_p521_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it \
      saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`, and keeps `out` in \
      `lr` (in `r10` during the calls); field elements are thirty-six 16-bit digits in Montgomery form, multiplied by \
      digit-by-digit Montgomery multiplication (CIOS, with `mul` and the accumulator in \
      `scratch`, in calls of `vg_p521_mul_mod_p` and the other functions of `p521_mont`) \
      with a final conditional subtraction; `[d]G` is a double-and-add ladder over \
      all 528 bits of the 66-byte encoding of `d`, with the complete addition formulas of Renes, \
      Costello and Batina for every addition and doubling and a masked selection for each bit; \
      and `Z⁻¹` is Fermat's, by square-and-always-multiply over the bits of `p - 2`. The result \
      (or zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only \
      on the pointers."]
    code := Impl.EcKey.Arm.publicKeyP521
    verified := Proof.EcKey.Arm.P521.pk_verified h.law }]

end VG.Generic.P521.Arm.EcP521
