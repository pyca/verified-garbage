import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx

/-!
# ECDSA over P-256 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-256's group law and
inversions `h`, the variant `Variants/P256/X86_64/Law.lean`, for each
multiplication: the baseline's, and BMI2's and ADX's, with the comb's
selection by AVX2 (`_adx`).
-/

namespace VG.Generic.P256.X86_64.EcdsaP256

/-- The function of `Spec.Ecdsa.P256.signApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def sign (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdsa.P256.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts)))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdsa.P256.signApi with
    name := Spec.Ecdsa.P256.signApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are four 64-bit words in Montgomery form, \
      " ++ Proof.Ecdsa.X86_64.mulNote adx ++ ". `[k]G` is a fixed-base comb of 7-bit signed digits: the 37 windows `k_j` of \
      `k`'s bits as Booth's digits `d_j = k_j + c_j - 128 c_(j+1)` from `-64` to `64` (`c_j` the \
      bit below window `j`, `c_0 = 0`), `[k]G = Σ [d_j 2^(7j)]G`, from 37 tables of `[m 2^(7j)]G` \
      (`m = 1 … 64`, affine, in Montgomery form) in the static `VG_P256_COMB` (148 KB), with no \
      doublings: each entry is selected in constant time by loading every entry of its table, " ++
      (if adx then "32 bytes at a time with AVX2, and keeping (`vpand`, `vpor`, under the mask of \
      `vpcmpeqd` of a counter and the magnitude, broadcast)" else "16 bytes at a time, and keeping \
      (`pand`, `por`)") ++ " the one of the digit's magnitude (or the point \
      at infinity for a zero digit), negated by a mask of its sign, and added, from `j = 0` up, to \
      a Jacobian accumulator by the mixed addition formulas madd-2004-hmv (8 multiplications and \
      3 squarings), which fail only for equal points: the accumulator, the sum of the digits' \
      terms below `j`, is never the entry, since `n` is prime, `[n]G` is the point at infinity \
      (which the proof's kernel computes) and the sums are smaller than any nonzero digit's term \
      modulo `n`. The entry replaces the sum where the accumulator is the point at infinity \
      (`Z = 0`), and the sum replaces the accumulator unless the digit is zero; the result is \
      `(XZ : Y : Z³)` in projective coordinates (with `Y = 1` for the point at infinity); the \
      inversions modulo `p` and `n` are by divsteps (Bernstein and Yang's safegcd, half-delta \
      form): 10 batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, \
      `g = Z`, or `n` and `k`), each giving a matrix of 64-bit entries that updates `f`, `g` \
      (divided by 2⁵⁹) and the coefficients `a`, `b` (divided by 2⁶⁴ modulo `p` or `n`, as in \
      Montgomery reduction), 590 divsteps in all, enough for 256-bit moduli by Bernstein and \
      Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or \
      its negation by `f`'s sign. The number of steps is fixed, so the time does not depend on \
      `Z` or `k`. The signature (or zeros) is selected by a mask, so the time depends only on the \
      pointers."])
    consts := Impl.Ecdsa.X86_64.p256.combConsts
    code
    contract := Spec.Ecdsa.P256.inst.signContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts)
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

/-- The function of `Spec.Ecdsa.P256.verifyApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def verify (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts)))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.Ecdsa.P256.verifyApi with
    name := Spec.Ecdsa.P256.verifyApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdsa.P256.verifyApi.doc (notes := ["The function is `vg_ecdsa_p256_sign" ++ (if adx then "_adx" else "") ++ "`'s setup, \
      field arithmetic, comb and inversions, with `vg_ecdh_p256" ++ (if adx then "_adx" else "") ++ "`'s checks of the public \
      key and its window method: it saves its caller's callee-saved registers in `scratch`; field elements and scalars \
      are four 64-bit words in Montgomery form, " ++ Proof.Ecdsa.X86_64.mulNote adx ++ ". The key is checked without \
      branches (its first byte, both coordinates below `p`, and the curve's equation), and \
      `[v]Q` is computed for the key's point if it is valid, else `G`, so it always runs on a \
      point of the curve. `s⁻¹` modulo `n` uses divsteps; `[u]G` uses the signature's comb \
      over 7-bit windows, directly indexing the static `VG_P256_COMB` with the public scalar `u`, and \
      `[v]Q` by `vg_ecdh_p256" ++ (if adx then "_adx" else "") ++ "`'s signed 4-bit windows (`v` recoded as `v + 8 Σ_{j<65} 16^j`, \
      a table of `[1 … 8]Q` in `scratch`, four Jacobian doublings and a complete addition of \
      the entry selected in constant time per digit); the two are added by the complete \
      addition formulas of Renes, Costello and Batina. The result is the conjunction of the \
      checks (the key, `r` and `s` in `[1, n-1]`, the sum not the point at infinity, and `x ≡ r` \
      modulo `n`) as a mask. The final comparison avoids a field inversion: in homogeneous \
      coordinates it checks `X = rZ`, or `X = (r+n)Z` when `r+n < p`, and rejects `Z = 0`. \
      Timing may depend on the public verification inputs, as permitted by the contract."])
    consts := Impl.Ecdsa.X86_64.p256.combConsts
    code
    contract := Spec.Ecdsa.P256.inst.verifyContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts)
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P256.curve) : List Artifact := [
  sign false Impl.Ecdsa.X86_64.signP256
    (Proof.Ecdsa.X86_64.sign_verified h.law (Proof.P256.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  verify false Impl.Ecdsa.Verify.X86_64.verifyP256
    (Proof.Ecdsa.Verify.X86_64.verify_verified h.law (Proof.P256.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  sign true Impl.Ecdsa.X86_64.signP256Adx
    (Proof.Ecdsa.X86_64.sign_verified_adx h.law (Proof.P256.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  verify true Impl.Ecdsa.Verify.X86_64.verifyP256Adx
    (Proof.Ecdsa.Verify.X86_64.verify_verified_adx h.law (Proof.P256.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P256.X86_64.EcdsaP256
