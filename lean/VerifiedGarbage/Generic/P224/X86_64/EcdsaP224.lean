import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointVerified

/-!
# ECDSA over P-224 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-224's group law and
inversions `h`, the variant `Variants/P224/X86_64/Law.lean`.
-/

namespace VG.Generic.P224.X86_64.EcdsaP224

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact := [
  { Spec.Ecdsa.P224.signApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P224.signApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are four 64-bit words in Montgomery \
      form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final conditional \
      subtraction; the 28-byte encodings are read and written a word at a time, the top word's \
      four bytes from the first eight or a byte at a time. `[k]G` is a fixed-base comb of 7-bit \
      signed digits: the 37 windows `k_j` of the bits of the four words of `k` as digits \
      `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) 2^(7j)]G`, from 37 \
      tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the static \
      `VG_P224_COMB` (148 KB), with no doublings: each entry is selected in constant time by \
      loading every entry of its table, 16 bytes at a time, and keeping (`pand`, `por`) the one \
      of the digit's magnitude (or the point at infinity for a zero digit), negated by a mask of \
      its sign, and added by the mixed complete addition formulas of Renes, Costello and Batina \
      for `a = -3` (Algorithm 5: the entry's `Z` is 1), the sum replacing the accumulator unless \
      the digit is zero; the inversion modulo `p` is by divsteps (Bernstein and Yang's safegcd, half-delta form): \
      10 batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), \
      each giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 590 \
      divsteps in all, enough for 256-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z`. `k⁻¹` modulo `n` is by \
      the same divsteps, from `f = n`, `g = k`. The signature (or \
      zeros) is selected by a mask, so the time depends only on the pointers."])
    consts := Impl.Ecdsa.X86_64.p224.combConsts
    code := Impl.Ecdsa.X86_64.signP224
    contract := Spec.Ecdsa.P224.inst.signContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p224.combConsts)
    verified := Proof.Ecdsa.X86_64.P224.sign_verified h.law (Proof.P224.combOk7 h.law) h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.P224.verifyApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P224.verifyApi.doc (notes := ["The function saves its caller's callee-saved \
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
      permitted by the contract."])
    consts := Impl.Ecdsa.X86_64.p224.combConsts
    code := Impl.Ecdsa.Verify.X86_64.jointVerifyP224
    contract := Spec.Ecdsa.P224.inst.verifyContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p224.combConsts)
    verified := Proof.Ecdsa.Verify.X86_64.P224.jointVerify_verified h.law (Proof.P224.combOk7 h.law) h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P224.X86_64.EcdsaP224
