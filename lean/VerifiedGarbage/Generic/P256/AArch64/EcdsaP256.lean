import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointVerified

/-!
# ECDSA over P-256 (FIPS 186-5) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

namespace VG.Generic.P256.AArch64.EcdsaP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P256.curve) : List Artifact := [
  { Spec.Ecdsa.P256.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves the callee-saved registers \
      `x19`–`x25` in `scratch`. Field elements and scalars are four 64-bit words in \
      Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` and \
      `umulh` and the multiplicand's words in registers; modulo `p`, `p ≡ -1 (mod 2⁶⁴)`, so each \
      step adds `t₀ (p + 1) / 2⁶⁴`, which takes two shifts and one product) with a final \
      conditional subtraction. `[k]G` is a fixed-base comb of 7-bit signed digits: the 37 windows `k_j` of `k`'s bits as \
      digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) 2^(7j)]G`, from 37 \
      tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the static `VG_P256_COMB` \
      (148 KB), with no doublings: each entry is selected in constant time by loading every entry \
      of its table and keeping, with `csel`, the one of the digit's magnitude (or the point at \
      infinity for a zero digit), negated by a mask of its sign, and added by the complete addition \
      formulas of Renes, Costello and Batina for `a = -3` (Algorithm 4: 12 products and 2 by `b`); the inversions modulo `p` and `n` are \
      by divsteps (Bernstein and Yang's safegcd, half-delta form): 10 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`, or `n` and `k`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p` or `n`, as in Montgomery reduction), 590 divsteps in all, enough for \
      256-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z` or `k`. The signature \
      (or zeros) is selected by a mask, so the time depends only on the pointers."])
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.Ecdsa.AArch64.signP256
    contract := Spec.Ecdsa.P256.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts)
    verified := Proof.Ecdsa.AArch64.sign_verified h.law h.inv (Proof.P256.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.P256.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P256.verifyApi.doc (notes := ["The function saves the callee-saved registers \
      `x19`–`x25` in its unchanged 8 KB scratch buffer. Field elements and scalars are four \
      64-bit words in Montgomery form; field squares use the specialized P-256 Montgomery \
      square. The key is checked without branches, and multiplication uses the key's point \
      if valid, else `G`. After computing `s⁻¹` modulo `n` by divsteps, `[u]G + [v]Q` uses one \
      joint Jacobian accumulator with width-7 and width-5 sparse signed digits, respectively. \
      Generator digits reuse the odd multiples in the first row of `VG_P256_COMB`. The eight \
      odd multiples of `Q` cache their Jacobian `Z²` and `Z³` values. The joint loop doubles \
      its accumulator in place and forwards field values between arithmetic operations, \
      then converts once to homogeneous coordinates. Verification compares the projective \
      x-coordinate with `r` and, when in range, `r + n`, without a field inversion. Table \
      lookups, skipped zero digits and exceptional-point branches depend on the public key, \
      digest and signature already declared public by the contract. The result combines \
      the key and scalar checks, rejection of infinity, and `x ≡ r` modulo `n` into a mask."])
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.Ecdsa.Verify.AArch64.P256Joint.verify
    contract := Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts)
    verified := Proof.Ecdsa.Verify.AArch64.jointVerify_verified h.law h.inv (Proof.P256.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P256.AArch64.EcdsaP256
