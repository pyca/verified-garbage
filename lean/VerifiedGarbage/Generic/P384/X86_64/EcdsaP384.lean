import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointVerified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx

/-!
# ECDSA over P-384 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-384's group law and
inversions `h`, the variant `Variants/P384/X86_64/Law.lean`, for each
multiplication: the baseline's, and BMI2's and ADX's, with the comb's
selection by AVX2 in signing (`_adx`).
-/

namespace VG.Generic.P384.X86_64.EcdsaP384

/-- The function of `Spec.Ecdsa.P384.signApi`, multiplying with BMI2 and ADX
and selecting the comb's entries with AVX2 (`adx`, `_adx`) or not: its `code`,
proven (`hv`), with no instruction writing `rsp` (`hsp`). -/
def sign (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdsa.P384.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts) 8))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdsa.P384.signApi with
    name := Spec.Ecdsa.P384.signApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdsa.P384.signApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are six 64-bit words in Montgomery form, \
      " ++ Proof.Ecdsa.X86_64.P384.mulNote adx ++ ". `[k]G` is a fixed-base comb of 7-bit signed digits: the 55 windows `k_j` of \
      `k`'s bits as digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) \
      2^(7j)]G`, from 55 tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the \
      static `VG_P384_COMB` (330 KB), with no doublings: each entry is selected in constant time \
      by loading every entry of its table, " ++ Proof.Ecdsa.X86_64.P384.selNote adx ++ " the one \
      of the digit's magnitude (or the point at infinity for a zero digit), negated by a mask of \
      its sign, and added by the mixed complete addition formulas of Renes, Costello and Batina \
      for `a = -3` (Algorithm 5: the entry's `Z` is 1), the sum replacing the accumulator \
      unless the digit is zero; the \
      inversion modulo `p` is by divsteps (Bernstein and Yang's safegcd, half-delta form): 15 \
      batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each \
      giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 885 \
      divsteps in all, enough for 384-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z`. `k⁻¹` modulo `n` is by \
      the same divsteps, from `f = n`, `g = k`. The signature (or zeros) \
      is selected by a mask, so the time depends only on the pointers."])
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    code
    contract := Spec.Ecdsa.P384.inst.signContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts) 8
    stack := 8
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

/-- The function of `Spec.Ecdsa.P384.verifyApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def verify (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts) 8))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdsa.P384.verifyApi with
    name := Spec.Ecdsa.P384.verifyApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdsa.P384.verifyApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are six 64-bit words in Montgomery form, \
      " ++ Proof.Ecdsa.X86_64.P384.mulNote adx ++ ". The public key is checked without branches \
      (its first byte, both coordinates below `p`, and the curve's equation); an invalid key is \
      replaced with `G` for the point operations and rejected by the final validity flag. \
      Divsteps computes `s⁻¹` modulo `n`, then `u = e/s` and `v = r/s`. Both public 384-bit \
      scalars are recoded as non-adjacent signed digits, width seven for `u` and width five for \
      `v`. A single Jacobian accumulator computes `[u]G + [v]Q` with 384 doublings, adding only \
      nonzero digits. Generator digits directly index odd multiples among the 64 affine entries \
      of the first row of the existing static `VG_P384_COMB`, added by mixed additions; peer \
      digits index eight odd multiples of `Q` in `scratch`, with cached squares and cubes of \
      their Z coordinates. Complete point operations cover infinity, equal points and opposite \
      points. Doubling is Jacobian, for `a = -3`, with `Z' = 2YZ` as a direct product, into a \
      temporary point copied back to the accumulator; on six words no register values are \
      forwarded between field operations. The final comparison squares the Jacobian Z \
      coordinate and checks `X = rZ²`, or `X = (r+n)Z²` when `r+n < p` (P-384 has \
      `n < p ≤ 2n`), without a field inversion. It rejects infinity and returns the \
      conjunction of the key, scalar-range and coordinate checks as 0 or 1. Timing may depend \
      on the public verification inputs, as permitted by the contract."])
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    code
    contract := Spec.Ecdsa.P384.inst.verifyContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts) 8
    stack := 8
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  sign false Impl.Ecdsa.X86_64.signP384
    (Proof.Ecdsa.X86_64.P384.sign_verified h.law (Proof.P384.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  verify false Impl.Ecdsa.Verify.X86_64.jointVerifyP384
    (Proof.Ecdsa.Verify.X86_64.P384.jointVerify_verified h.law (Proof.P384.combOk7 h.law) h.inv)
    (Code.all_of_allInstrs (by lit_decide)),
  sign true Impl.Ecdsa.X86_64.signP384Adx
    (Proof.Ecdsa.X86_64.P384.sign_verified_adx h.law (Proof.P384.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  verify true Impl.Ecdsa.Verify.X86_64.jointVerifyP384Adx
    (Proof.Ecdsa.Verify.X86_64.P384.jointVerify_verified_adx h.law (Proof.P384.combOk7 h.law) h.inv)
    (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P384.X86_64.EcdsaP384
