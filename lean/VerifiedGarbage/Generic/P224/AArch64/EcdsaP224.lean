module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.AArch64
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P224.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P224.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.P224.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Spec.Weierstrass.Mul
import VerifiedGarbage.Impl.Ecdh.P224.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Spec.Weierstrass.Mul

/-!
# ECDSA over P-224 (FIPS 186-5) on AArch64

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.AArch64.EcdsaP224

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.P224.signApi.artifact AArch64.target {
    notes := ["The function saves the callee-saved registers \
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
      Batina for `a = -3` (Algorithm 4: 12 products and 2 by `b`); the inversions modulo `p` \
      and `n` are calls of `vg_p224_inv_mod_p` and `vg_p224_inv_mod_n`, by divsteps (Bernstein and Yang's safegcd, half-delta form): 10 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`, or `n` and `k`), \
      each giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p` or `n`, as in Montgomery reduction), 590 \
      divsteps in all, enough for 256-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z` or `k`. The signature (or \
      zeros) is selected by a mask, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p224.combConsts
    code := Impl.Ecdsa.AArch64.signP224
    verified := Proof.Ecdsa.AArch64.P224.sign_verified h.law h.inv (Proof.P224.combOk7 h.law) },
  Spec.Ecdsa.P224.verifyApi.artifact AArch64.target {
    notes := ["The function is `vg_ecdsa_p224_sign`'s \
      setup, field arithmetic, comb and inversions, with `vg_ecdh_p224`'s checks of the public \
      key: it saves the callee-saved registers `x19`–`x25` in `scratch`; field elements and \
      scalars are four 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and `umulh` and the multiplicand's words in registers; \
      each reduction step multiplies the accumulator's low word by `-m⁻¹ mod 2⁶⁴` and adds that \
      multiple of the modulus) with a final conditional subtraction. The key is checked without \
      branches (its first byte, both coordinates below `p`, and the curve's equation), and \
      `[v]Q` is computed for the key's point if it is valid, else `G`, so always on a point of \
      the curve. `s⁻¹` modulo `n` is a call of `vg_p224_inv_mod_n`, by the signature's divsteps; `[u]G` is the signature's comb over the 7-bit windows of `u` (from the static `VG_P224_COMB`, reading the entry of each \
      digit of the public `u` directly rather than scanning its table), and `[v]Q` `vg_ecdh_p224`'s signed 4-bit windows (65 digits of `v + 8 \
      Σ_{j<65} 16^j`, four doublings in Jacobian coordinates and a constant-time selection from \
      a table of `[1 … 8]Q` each), with the complete formulas of Renes, Costello and Batina for \
      `a = -3`, which also add the two. The result is the conjunction of the checks (the key, \
      `r` and `s` in `[1, n-1]`, the sum not the point at infinity, and `X = rZ` or, when `r + n < p`, `X = (r + n)Z`, compared in projective coordinates without inverting `Z`) as a \
      mask, so the \
      comb's addresses depend on `u`, from the digest and the signature, and the rest of the \
      time only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p224.combConsts
    code := Impl.Ecdsa.Verify.AArch64.verifyP224
    verified := Proof.Ecdsa.Verify.AArch64.P224.verify_verified h.law h.inv (Proof.P224.combOk7 h.law) }]

end VG.Generic.P224.AArch64.EcdsaP224
