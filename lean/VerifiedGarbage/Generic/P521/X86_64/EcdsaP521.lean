import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.HasLawOrd
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.LitAdx
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.LitAdx

/-!
# ECDSA over P-521 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-521's group law and
inversions `h`, the variant
`Variants/P521/X86_64/Law.lean`, for each multiplication modulo `p`: the
baseline's, and BMI2's and ADX's (`_adx`).
-/

namespace VG.Generic.P521.X86_64.EcdsaP521

/-- The function of `Spec.Ecdsa.P521.signApi`, multiplying modulo `p` with BMI2
and ADX and selecting the comb's entries with AVX2 (`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction
writing `rsp` (`hsp`). -/
def sign (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdsa.P521.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts)))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdsa.P521.signApi with
    name := Spec.Ecdsa.P521.signApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdsa.P521.signApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are nine 64-bit words in Montgomery \
      form, " ++ Proof.Ecdsa.X86_64.P521.mulNote adx ++ ", and \
      modulo `n` by columns too (finely integrated product scanning: each column also adds the \
      reduction's products by `n`'s words, and each of the first nine computes its multiplier \
      `u = t₀ (-n⁻¹) mod 2⁶⁴`), each with a final conditional subtraction; the 66-byte encodings are read and \
      written a word at a time, the top word's two bytes from the first eight or a byte at a \
      time, and the hash's integer is shifted right by its last 7 bits. `[k]G` is a fixed-base \
      comb of 7-bit signed digits: the 83 windows `k_j` of `k`'s bits as digits `k_j - 64` from \
      `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) 2^(7j)]G`, from 83 tables of \
      `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the static `VG_P521_COMB` \
      (747 KB), with no doublings: each entry is selected in constant time by loading every \
      entry of its table, " ++ Proof.Ecdsa.X86_64.P521.selNote adx ++ " the one of the digit's \
      magnitude (or the point at infinity for a zero digit), negated by a mask of its sign, and \
      added by the mixed complete addition formulas of Renes, Costello and Batina \
      for `a = -3` (Algorithm 5: the entry's `Z` is 1), the sum replacing the accumulator \
      unless the digit is zero; the \
      inversion modulo `p` is by divsteps (Bernstein and Yang's safegcd, half-delta form): 23 \
      batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each \
      giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 1357 \
      divsteps in all, enough for 576-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z`. `k⁻¹` modulo `n` is by \
      the same divsteps, from `f = n`, `g = k`. The signature (or \
      zeros) is selected by a mask, so the time depends only on the pointers."])
    consts := Impl.Ecdsa.X86_64.p521.combConsts
    code
    contract := Spec.Ecdsa.P521.inst.signContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts)
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

/-- The function of `Spec.Ecdsa.P521.verifyApi`, multiplying modulo `p` with
BMI2 and ADX (`adx`, `_adx`) or not: its `code`, proven (`hv`), with no
instruction writing `rsp` (`hsp`). -/
def verify (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts)))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdsa.P521.verifyApi with
    name := Spec.Ecdsa.P521.verifyApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdsa.P521.verifyApi.doc (notes := ["The function is `vg_ecdsa_p521_sign" ++ (if adx then "_adx" else "") ++ "`'s setup, \
      field arithmetic and inversions, with `vg_ecdh_p521" ++ (if adx then "_adx" else "") ++ "`'s checks of the public key and window \
      method: it \
      saves its caller's callee-saved registers in `scratch`; field elements and scalars are nine \
      64-bit words in Montgomery form, " ++ Proof.Ecdsa.X86_64.P521.mulNote adx ++ ", and \
      modulo `n` by columns too (finely integrated product scanning: each column also adds the \
      reduction's products by `n`'s words, and each of the first nine computes its multiplier \
      `u = t₀ (-n⁻¹) mod 2⁶⁴`), each with a final conditional subtraction, and the hash's \
      integer is shifted right by its last 7 bits. The key is checked without branches (its \
      first byte, both coordinates below `p`, and the curve's equation), and the window method \
      multiplies the key's point if it is valid, else `G`, so it always runs on a point of the \
      curve. `s⁻¹` modulo `n` and `Z⁻¹` are by the signature's divsteps; `[u]G` is the \
      signature's comb over the 7-bit windows of `u` (from the static `VG_P521_COMB`), and \
      `[v]Q` by `vg_ecdh_p521" ++ (if adx then "_adx" else "") ++ "`'s signed 4-bit windows over the 133 digits of `v`, with the \
      complete addition formulas of Renes, Costello and Batina, which also add the two. The \
      result is the conjunction of the checks (the key, `r` and `s` in `[1, n-1]`, the sum not \
      the point at infinity, and `x ≡ r` modulo `n`) as a mask, so the time depends only on the \
      pointers, although the contract would let every input affect it."])
    consts := Impl.Ecdsa.X86_64.p521.combConsts
    code
    contract := Spec.Ecdsa.P521.inst.verifyContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts)
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  sign false Impl.Ecdsa.X86_64.signP521
    (Proof.Ecdsa.X86_64.P521.sign_verified h.law (Proof.P521.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  verify false Impl.Ecdsa.Verify.X86_64.verifyP521
    (Proof.Ecdsa.Verify.X86_64.P521.verify_verified h.law (Proof.P521.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  sign true Impl.Ecdsa.X86_64.signP521Adx
    (Proof.Ecdsa.X86_64.P521.sign_verified_adx h.law (Proof.P521.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  verify true Impl.Ecdsa.Verify.X86_64.verifyP521Adx
    (Proof.Ecdsa.Verify.X86_64.P521.verify_verified_adx h.law (Proof.P521.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P521.X86_64.EcdsaP521
