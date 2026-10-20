module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Checks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafPoints
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.CoZTable
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Checks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafPoints
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-!
# ECDSA over P-384 (FIPS 186-5) on AArch64

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.AArch64.EcdsaP384

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.P384.signApi.artifact AArch64.target {
    notes := ["The function saves the callee-saved registers \
      `x19`–`x25` in `scratch`. Field elements and scalars are six 64-bit words in \
      Montgomery form, field elements multiplied by calls of `vg_p384_mul_mod_p` (the schedule of \
      s2n-bignum's `bignum_montmul_p384_alt`: the full twelve-word product, six short Montgomery \
      reductions by the three nonzero words of `2^384 - p`, and a final conditional subtraction), \
      and scalars multiplied by calls of `vg_p384_mul_mod_n` (word-by-word Montgomery \
      multiplication, CIOS, with a final conditional subtraction). `[k]G` is a fixed-base comb of \
      7-bit signed digits: the 55 windows `k_j` of \
      `k`'s bits as digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) \
      2^(7j)]G`, from 55 tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the \
      static `VG_P384_COMB` (330 KB), with no doublings: each entry is selected in constant time by \
      loading every entry of its table and keeping, with `csel`, the one of the digit's magnitude \
      (or the point at infinity for a zero digit), its `x` in one pass over the table and its `y` \
      in another, negated by a mask of its sign, and added by the complete addition formulas of \
      Renes, Costello and Batina for `a = -3` (Algorithm 4: 12 products and 2 by `b`); the \
      inversions modulo `p` and `n` are calls of `vg_p384_inv_mod_p` and `vg_p384_inv_mod_n`, \
      by divsteps (Bernstein and Yang's safegcd, half-delta form): 15 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`, or `n` and `k`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p` or `n`, as in Montgomery reduction), 885 divsteps in all, enough for \
      384-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z` or `k`. The signature \
      (or zeros) is selected by a mask, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p384.combConsts
    code := Impl.Ecdsa.AArch64.signP384
    verified := Proof.Ecdsa.AArch64.P384.sign_verified h.law h.inv (Proof.P384.combOk7 h.law) },
  Spec.Ecdsa.P384.verifyApi.artifact AArch64.target {
    notes := ["The function is `vg_ecdsa_p384_sign`'s setup, \
      field arithmetic, comb and inversions, with `vg_ecdh_p384`'s checks of the public key: it \
      saves the callee-saved registers `x19`–`x25` in `scratch`; field elements and \
      scalars are six 64-bit words in Montgomery form, field elements multiplied and squared by \
      calls of `vg_p384_mul_mod_p` and `vg_p384_sqr_mod_p` (the schedules of s2n-bignum's \
      `bignum_montmul_p384_alt` and `bignum_montsqr_p384_alt`: the full twelve-word product or \
      square, six short Montgomery reductions by the three nonzero words of `2^384 - p`, and a \
      final conditional subtraction), and scalars multiplied by calls of `vg_p384_mul_mod_n` \
      (word-by-word Montgomery multiplication, CIOS, with a final conditional subtraction). The \
      key is checked without branches \
      (its first byte, both coordinates below `p`, and the curve's equation), and `[v]Q` is \
      computed for the key's point if it is valid, else `G`, so always on a point of the curve. \
      `s⁻¹` modulo `n` is a call of `vg_p384_inv_mod_n`, by the signature's divsteps; `[u]G` is the \
      signature's comb over the 7-bit windows of `u` (from the static `VG_P384_COMB`, reading the entry of each \
      digit of the public `u` directly rather than scanning its table), and `[v]Q` the \
      width-5 non-adjacent form of the public `v` (its 385 digits in `{0, ±1, ±3, …, ±15}` \
      recoded into `scratch`, a table of `[1]Q, [3]Q, …, [15]Q` built by co-Z arithmetic (a \
      doubling of the affine `Q` giving `2Q` and `Q` at one `Z`, then seven additions of `2Q` \
      sharing each sum's `Z`, never `±2Q` itself since the curve's order is prime), each entry's `Z²` and \
      `Z³` kept next to the table, and for each digit from the top a \
      doubling in Jacobian coordinates and, for a digit other than 0, a complete Jacobian addition \
      of the entry it selects, read directly, with its `y` negated for a negative digit and its \
      `Z²` and `Z³` read rather than computed; the \
      products and squares are calls of `vg_p384_mul_mod_p` and `vg_p384_sqr_mod_p`), converted \
      to projective coordinates and added to `[u]G` by the complete formulas of Renes, Costello \
      and Batina for `a = -3`. The result is the conjunction of the checks (the key, \
      `r` and `s` in `[1, n-1]`, the sum not the point at infinity, and `X = rZ` or, when `r + n < p`, `X = (r + n)Z`, compared in projective coordinates without inverting `Z`) as a mask, so the \
      comb's addresses depend on `u`, from the digest and the signature, the non-adjacent \
      form's branches and addresses on `v`, from the signature, and on the key, and the rest of \
      the time only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p384.combConsts
    code := Impl.Ecdsa.Verify.AArch64.verifyP384
    verified := Proof.Ecdsa.Verify.AArch64.P384.verify_verified h.law h.prime h.inv (Proof.P384.combOk7 h.law) }]

end VG.Generic.P384.AArch64.EcdsaP384
