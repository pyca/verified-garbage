module

public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointVerified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointLit
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointVerified
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Impl.Ecdh.P224.X86_64
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86_64.Check
public import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.P224.Point
public import VerifiedGarbage.Proof.P224.X86_64.JointLayout
public import VerifiedGarbage.Proof.P224.X86_64.NafTableTiming
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafOdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedPoint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMulTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointTables
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrepTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTable
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCopy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableFields
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingStep
public import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Impl.Ecdh.P224.X86_64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.P224.X86_64.JointLayout
import VerifiedGarbage.Proof.P224.X86_64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafOdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedLoad
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMulTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointTables
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrepTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop

/-!
# ECDSA over P-224 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-224's group law and
inversions `h`, the variant `Variants/P224/X86_64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.X86_64.EcdsaP224

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.P224.signApi.artifact X86_64.target {
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are four 64-bit words in Montgomery \
      form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final conditional \
      subtraction; the 28-byte encodings are read and written a word at a time, the top word's \
      four bytes from the first eight or a byte at a time. `[k]G` is a call of `vg_p224_mul_base`, \
      which expands `k` into a table of its bits and runs a fixed-base comb of 7-bit signed \
      digits: the 37 windows `k_j` of the bits of the four words of `k` as digits \
      `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) 2^(7j)]G`, from 37 \
      tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the static \
      `VG_P224_COMB` (148 KB), with no doublings: each entry is selected in constant time by \
      loading every entry of its table, 16 bytes at a time, and keeping (`pand`, `por`) the one \
      of the digit's magnitude (or the point at infinity for a zero digit), negated by a mask of \
      its sign, and added by the mixed complete addition formulas of Renes, Costello and Batina \
      for `a = -3` (Algorithm 5: the entry's `Z` is 1), the sum replacing the accumulator unless \
      the digit is zero; the inversion modulo `p` is a call of `vg_p224_inv_mod_p`, by divsteps \
      (Bernstein and Yang's safegcd, half-delta form): 10 batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), \
      each giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 590 \
      divsteps in all, enough for 256-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z`. `k⁻¹` modulo `n` is by \
      the same divsteps, from `f = n`, `g = k`, a call of `vg_p224_inv_mod_n`. The signature (or \
      zeros) is selected by a mask, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.X86_64.p224.combConsts
    code := Impl.Ecdsa.X86_64.signP224
    stack := 8
    verified := Proof.Ecdsa.X86_64.P224.sign_verified h.law (Proof.P224.combOk7 h.law) h.inv },
  Spec.Ecdsa.P224.verifyApi.artifact X86_64.target {
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are four 64-bit words in Montgomery form, \
      multiplied by word-by-word Montgomery multiplication (CIOS) with a final conditional \
      subtraction. The public key is checked without branches (its first byte, both coordinates \
      below `p`, and the curve's equation); an invalid key is replaced with `G` for the point \
      operations and rejected by the final validity flag. Divsteps computes `s⁻¹` modulo `n`, then \
      `u = e/s` and `v = r/s`. Both public scalars are recoded, over the 256 bits of their four \
      words, as non-adjacent signed digits, width seven for `u` and width five for `v`. A single Jacobian \
      accumulator computes `[u]G + [v]Q` with 256 doublings, adding only nonzero digits. \
      Generator digits directly index odd multiples among the 64 affine entries of the first row \
      of the existing static `VG_P224_COMB`, added by mixed additions; peer digits index eight odd \
      multiples of `Q` in `scratch`, with cached squares and cubes of their Z coordinates. \
      Complete point operations cover infinity, equal points and opposite points. Doubling is \
      Jacobian, for `a = -3`, with `Z' = 2YZ` as a direct product, into a temporary point copied \
      back to the accumulator. The final comparison squares the Jacobian Z coordinate and checks \
      `X = rZ²`, or `X = (r+n)Z²` when `r+n < p` (P-224 has `n < p ≤ 2n`), without a field \
      inversion. It rejects infinity and returns the conjunction of the key, scalar-range and \
      coordinate checks as 0 or 1. Timing may depend on the public verification inputs, as \
      permitted by the contract."]
    consts := Impl.Ecdsa.X86_64.p224.combConsts
    code := Impl.Ecdsa.Verify.X86_64.jointVerifyP224
    stack := 8
    verified := Proof.Ecdsa.Verify.X86_64.P224.jointVerify_verified h.law (Proof.P224.combOk7 h.law) h.inv }]

end VG.Generic.P224.X86_64.EcdsaP224
