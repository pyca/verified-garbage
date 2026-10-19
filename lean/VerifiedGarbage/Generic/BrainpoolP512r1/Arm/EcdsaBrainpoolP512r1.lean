module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.Arm
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA over brainpoolP512r1 (FIPS 186-5) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.Arm.EcdsaBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP512r1.signApi.artifact Arm.target {
    notes := ["The function saves the callee-saved registers \
      `r4`–`r11` and `lr` in `scratch`, and keeps `out` in `lr` (in `r10` during the calls). Field \
      elements and scalars are \
      thirty-two 16-bit digits in Montgomery form, multiplied by digit-by-digit Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of \
      `vg_brainpoolp512r1_mul_mod_p` and the other functions of `brainpoolp512r1_mont`) with a final \
      conditional subtraction. `[k]G` is a double-and-add ladder over all 512 bits of `k`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling and a masked selection for each bit; the inversions modulo `p` and `n` are \
      Fermat's, by square-and-always-multiply over the bits of `p - 2` and `n - 2`. The \
      signature (or zeros) is selected by a mask, so the time depends only on the pointers."]
    code := Impl.Ecdsa.Arm.signBrainpoolP512r1
    verified := Proof.Ecdsa.Arm.BrainpoolP512r1.sign_verified h.law },
  Spec.Ecdsa.BrainpoolP512r1.verifyApi.artifact Arm.target {
    notes := ["The function is `vg_ecdsa_brainpoolp512r1_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_brainpoolp512r1`'s checks of the public key: it \
      saves the callee-saved registers `r4`–`r11` and `lr` in `scratch`; field elements and \
      scalars are thirty-two 16-bit digits in Montgomery form, multiplied by digit-by-digit \
      Montgomery multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of \
      `vg_brainpoolp512r1_mul_mod_p` and the other functions of `brainpoolp512r1_mont`) with a final \
      conditional subtraction. The key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and the second ladder multiplies the \
      key's point if it is valid, else `G`, so it always runs on a point of the curve. `s⁻¹` \
      modulo `n` and `Z⁻¹` are Fermat's, by square-and-always-multiply; `[u]G` and `[v]Q` are \
      double-and-add ladders over all 512 bits of `u` and `v`, with the complete addition \
      formulas of Renes, Costello and Batina, which also add the two. The result is the \
      conjunction of the checks (the key, `r` and `s` in `[1, n-1]`, the sum not the point at \
      infinity, and `x ≡ r` modulo `n`) as a mask, so the time depends only on the pointers, \
      although the contract would let every input affect it."]
    code := Impl.Ecdsa.Verify.Arm.verifyBrainpoolP512r1
    verified := Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.verify_verified h.law }]

end VG.Generic.BrainpoolP512r1.Arm.EcdsaBrainpoolP512r1
