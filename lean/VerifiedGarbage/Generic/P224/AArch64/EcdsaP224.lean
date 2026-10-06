import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
import VerifiedGarbage.Impl.Ecdsa.Verify.P224.AArch64
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Verified

/-!
# ECDSA over P-224 (FIPS 186-5) on AArch64

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/AArch64/Law.lean`.
-/

namespace VG.Generic.P224.AArch64.EcdsaP224

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  { Spec.Ecdsa.P224.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P224.signApi.doc (notes := ["The function saves the callee-saved registers \
      `x19`–`x25` in `scratch`. Field elements and scalars are four 64-bit words in Montgomery \
      form, multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` and `umulh` \
      and the multiplicand's words in registers; each reduction step multiplies the \
      accumulator's low word by `-m⁻¹ mod 2⁶⁴` and adds that multiple of the modulus) with a \
      final conditional subtraction. `[k]G` is a fixed-base comb of 7-bit signed digits: the 37 \
      windows `k_j` of `k`'s bits as digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ \
      2^(7j)]G + Σ [(k_j - 64) 2^(7j)]G`, from 37 tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, \
      in Montgomery form) in the static `VG_P224_COMB` (148 KB), with no doublings: each entry \
      is selected in constant time by loading every entry of its table and keeping, with `csel`, \
      the one of the digit's magnitude (or the point at infinity for a zero digit), negated by a \
      mask of its sign, and added by the complete addition formulas of Renes, Costello and \
      Batina for `a = -3` (Algorithm 4: 12 products and 2 by `b`); the inversion modulo `p` is \
      by divsteps (Bernstein and Yang's safegcd, half-delta form): 10 batches of 59 divsteps on \
      the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 590 divsteps in all, enough for \
      256-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and \
      `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. The number of steps is fixed, \
      so the time does not depend on `Z`; `k⁻¹` modulo `n` is Fermat's, by a chain of sliding \
      4-bit windows over `n - 2`, fixed by the code (squarings and products by a table of odd \
      powers). The signature (or zeros) is selected by a mask, so the time depends only on the \
      pointers."])
    consts := Impl.Ecdsa.AArch64.p224.combConsts
    code := Impl.Ecdsa.AArch64.signP224
    contract := Spec.Ecdsa.P224.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts)
    verified := Proof.Ecdsa.AArch64.P224.sign_verified h.law h.inv (Proof.P224.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.P224.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P224.verifyApi.doc (notes := ["The function is `vg_ecdsa_p224_sign`'s \
      setup, field arithmetic, comb and inversions, with `vg_ecdh_p224`'s checks of the public \
      key: it saves the callee-saved registers `x19`–`x25` in `scratch`; field elements and \
      scalars are four 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and `umulh` and the multiplicand's words in registers; \
      each reduction step multiplies the accumulator's low word by `-m⁻¹ mod 2⁶⁴` and adds that \
      multiple of the modulus) with a final conditional subtraction. The key is checked without \
      branches (its first byte, both coordinates below `p`, and the curve's equation), and \
      `[v]Q` is computed for the key's point if it is valid, else `G`, so always on a point of \
      the curve. `s⁻¹` modulo `n` is Fermat's, by the signature's chain, and `Z⁻¹` by its \
      divsteps; `[u]G` is the signature's comb over the 7-bit windows of `u` (from the static \
      `VG_P224_COMB`), and `[v]Q` `vg_ecdh_p224`'s signed 4-bit windows (65 digits of `v + 8 \
      Σ_{j<65} 16^j`, four doublings in Jacobian coordinates and a constant-time selection from \
      a table of `[1 … 8]Q` each), with the complete formulas of Renes, Costello and Batina for \
      `a = -3`, which also add the two. The result is the conjunction of the checks (the key, \
      `r` and `s` in `[1, n-1]`, the sum not the point at infinity, and `x ≡ r` modulo `n`) as a \
      mask, so the time depends only on the pointers, although the contract would let every \
      input affect it."])
    consts := Impl.Ecdsa.AArch64.p224.combConsts
    code := Impl.Ecdsa.Verify.AArch64.verifyP224
    contract := Spec.Ecdsa.P224.inst.verifyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts)
    verified := Proof.Ecdsa.Verify.AArch64.P224.verify_verified h.law h.inv (Proof.P224.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P224.AArch64.EcdsaP224
