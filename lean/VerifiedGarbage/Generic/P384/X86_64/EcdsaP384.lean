module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
public import VerifiedGarbage.Proof.P384.Comb7
public import VerifiedGarbage.Proof.P384.GTable9 -- shake: keep (the artifacts' bodies use `gtabOk9`)
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Impl.Ecdh.P384.X86_64
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86_64.Check
public import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.VerifyLit
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.P384.X86_64.JointLayout
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
import VerifiedGarbage.Impl.Ecdh.P384.X86_64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.VerifyLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.P384.X86_64.JointLayout
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
# ECDSA over P-384 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-384's group law and
inversions `h`, the variant `Variants/P384/X86_64/Law.lean`, for each
multiplication: the baseline's, and BMI2's and ADX's, with the comb's
selection by AVX2 in signing (`_adx`).
-/

@[expose] public section

namespace VG.Generic.P384.X86_64.EcdsaP384

/-- The function of `Spec.Ecdsa.P384.signApi`, multiplying with BMI2 and ADX
and selecting the comb's entries with AVX2 (`adx`, `_adx`) or not: its `code`,
proven (`hv`), with no instruction writing `rsp` (`hsp`). -/
def sign (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdsa.P384.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts) 8))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true := by sp_safe) : Artifact :=
  Spec.Ecdsa.P384.signApi.artifact X86_64.target {
    suffix := (if adx then "_adx" else "")
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are six 64-bit words in Montgomery form, \
      " ++ Proof.Ecdsa.X86_64.P384.mulNote adx ++ ". `[k]G` is a call of `vg_p384_mul_base" ++ (if adx then "_adx" else "") ++ "`, which \
      expands `k` into a table of its bits and runs a fixed-base comb of 7-bit signed digits, its \
      products written out: the 55 windows `k_j` of \
      `k`'s bits as digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) \
      2^(7j)]G`, from 55 tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the \
      static `VG_P384_COMB` (330 KB), with no doublings: each entry is selected in constant time \
      by loading every entry of its table, " ++ Proof.Ecdsa.X86_64.P384.selNote adx ++ " the one \
      of the digit's magnitude (or the point at infinity for a zero digit), negated by a mask of \
      its sign, and added by the mixed complete addition formulas of Renes, Costello and Batina \
      for `a = -3` (Algorithm 5: the entry's `Z` is 1), the sum replacing the accumulator \
      unless the digit is zero; the \
      inversion modulo `p` is a call of `vg_p384_inv_mod_p" ++ (if adx then "_adx" else "") ++ "`, \
      by divsteps (Bernstein and Yang's safegcd, half-delta form): 15 \
      batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each \
      giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 885 \
      divsteps in all, enough for 384-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z`. `k⁻¹` modulo `n` is by \
      the same divsteps, from `f = n`, `g = k`, a call of `vg_p384_inv_mod_n" ++
      (if adx then "_adx" else "") ++ "`. The signature (or zeros) \
      is selected by a mask, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    code
    stack := 8
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

/-- The function of `Spec.Ecdsa.P384.verifyApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def verify (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts Impl.P384.X86_64.p384v.combConsts) 8))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true := by sp_safe) : Artifact :=
  Spec.Ecdsa.P384.verifyApi.artifact X86_64.target {
    suffix := (if adx then "_adx" else "")
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are six 64-bit words in Montgomery form, \
      " ++ Proof.Ecdsa.X86_64.P384.mulNote adx ++ ". The public key is checked without branches \
      (its first byte, both coordinates below `p`, and the curve's equation); an invalid key is \
      replaced with `G` for the point operations and rejected by the final validity flag. \
      Divsteps computes `s⁻¹` modulo `n` (a call of `vg_p384_inv_mod_n" ++
      (if adx then "_adx" else "") ++ "`), then `u = e/s` and `v = r/s`. Both public 384-bit \
      scalars are recoded as non-adjacent signed digits, width nine for `u` (sixteen bits each) \
      and width five for `v`. A single Jacobian accumulator computes `[u]G + [v]Q` with 384 \
      doublings, adding only nonzero digits. Generator digits directly index the affine odd \
      multiples `[m]G`, `m ≤ 255`, in the static `VG_P384_GTAB` of `[m]G` for `m = 1 … 256` \
      (24 KB, in Montgomery form), added by mixed additions; peer digits index eight odd multiples of `Q` in `scratch`, with cached \
      squares and cubes of their Z coordinates, built by co-Z arithmetic (Goundar, Joye, Miyaji, \
      Rivain and Venelli): DBLU of the affine `Q` gives `2Q` and `Q` at one `Z`, then seven ZADDU \
      (5 multiplications and 2 squarings each) add `2Q` and leave it at the sum's `Z`; the \
      operands are never equal or opposite, since `n` is prime. The digits' additions are calls of \
      `vg_p384_jac_add_cached` (the peer's digits) and `vg_p384_jac_add_affine` (the generator's)" ++
      (if adx then ", their `_adx` forms," else "") ++ " which cover infinity, equal points and \
      opposite points; the doubling and the table of odd multiples are inline. Doubling is Jacobian, for \
      `a = -3`, with `Z' = 2YZ` as a direct product, in place: each coordinate of the accumulator is \
      read for the last time before it is written, so no copy" ++
      (if adx then ", and its small multiples are fused into three steps `C a - D b mod p` \
        (s2n-bignum's sequence)" else "") ++ "; on six words no register values are forwarded \
      between field operations. The final comparison squares the Jacobian Z \
      coordinate and checks `X = rZ²`, or `X = (r+n)Z²` when `r+n < p` (P-384 has \
      `n < p ≤ 2n`), without a field inversion. It rejects infinity and returns the \
      conjunction of the key, scalar-range and coordinate checks as 0 or 1. Timing may depend \
      on the public verification inputs, as permitted by the contract."]
    consts := Impl.P384.X86_64.p384v.combConsts
    code
    stack := 8
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  sign false Impl.Ecdsa.X86_64.signP384
    (Proof.Ecdsa.X86_64.P384.sign_verified h.law (Proof.P384.combOk7 h.law) h.inv),
  verify false Impl.Ecdsa.Verify.X86_64.jointVerifyP384
    (Proof.Ecdsa.Verify.X86_64.P384.jointVerify_verified h.law (Proof.P384.gtabOk9 h.law) h.inv
      h.prime),
  sign true Impl.Ecdsa.X86_64.signP384Adx
    (Proof.Ecdsa.X86_64.P384.sign_verified_adx h.law (Proof.P384.combOk7 h.law) h.inv),
  verify true Impl.Ecdsa.Verify.X86_64.jointVerifyP384Adx
    (Proof.Ecdsa.Verify.X86_64.P384.jointVerify_verified_adx h.law (Proof.P384.gtabOk9 h.law) h.inv
      h.prime)]

end VG.Generic.P384.X86_64.EcdsaP384
