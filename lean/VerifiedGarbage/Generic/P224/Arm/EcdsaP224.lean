module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.Arm
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Verified
import VerifiedGarbage.Impl.Ecdsa.P224.Arm
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.Arm.Peer
public import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
public import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
public import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Final
public import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.P224.Point
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
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Final
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.P224.Point
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
# ECDSA over P-224 (FIPS 186-5) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.Arm.EcdsaP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.P224.signApi.artifact Arm.target {
    notes := ["The function saves the callee-saved registers \
      `r4`–`r11` and `lr` in `scratch`, and keeps `out` in `lr` (in `r10` during the calls). Field \
      elements and scalars are \
      sixteen 16-bit digits in Montgomery form, multiplied by digit-by-digit Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of \
      `vg_p224_mul_mod_p` and the other functions of `p224_mont`) with a final \
      conditional subtraction. `[k]G` is a double-and-add ladder over all 256 bits of `k`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling (calls of `vg_p224_point_double` and \
      `vg_p224_point_add`) and a masked selection for each bit; the inversions modulo `p` and `n` are \
      Fermat's, by square-and-always-multiply over the bits of `p - 2` and `n - 2`. The \
      signature (or zeros) is selected by a mask, so the time depends only on the pointers."]
    code := Impl.Ecdsa.Arm.signP224
    verified := Proof.Ecdsa.Arm.P224.sign_verified h.law },
  Spec.Ecdsa.P224.verifyApi.artifact Arm.target {
    notes := ["The function is `vg_ecdsa_p224_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_p224`'s checks of the public key: it \
      saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`; field elements and \
      scalars are sixteen 16-bit digits in Montgomery form, multiplied by digit-by-digit \
      Montgomery multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of \
      `vg_p224_mul_mod_p` and the other functions of `p224_mont`) with a final \
      conditional subtraction. The key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and the second ladder multiplies the \
      key's point if it is valid, else `G`, so it always runs on a point of the curve. `s⁻¹` \
      modulo `n` and `Z⁻¹` are Fermat's, by square-and-always-multiply; `[u]G` and `[v]Q` are \
      double-and-add ladders over all 256 bits of `u` and `v`, with the complete addition \
      formulas of Renes, Costello and Batina (calls of `vg_p224_point_double` and \
      `vg_p224_point_add` in the ladders), which also add the two. The result is the \
      conjunction of the checks (the key, `r` and `s` in `[1, n-1]`, the sum not the point at \
      infinity, and `x ≡ r` modulo `n`) as a mask, so the time depends only on the pointers, \
      although the contract would let every input affect it."]
    code := Impl.Ecdsa.Verify.Arm.verifyP224
    verified := Proof.Ecdsa.Verify.Arm.P224.verify_verified h.law }]

end VG.Generic.P224.Arm.EcdsaP224
