module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Halve
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Residue
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero

/-!
# An FFDH parameter candidate on AArch64: the shape's flag

`shapeFlag g w c`, the value `fBad` ends with for the candidate `c` in `w`
words: zero exactly when `c` has the generator's shape and `c` and
`(c − 1) / 2` pass `primeShape` and RSA's trial division,
`obviouslyComposite` (`shapeFlag_zero`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.Proof.Bignum VG.Proof.RsaKeyGen.AArch64 VG.Spec.Ffdh VG.Impl.RsaKeyGen

/-- The flag of the shape checks of `c`. -/
def shapeFlag (g w c : Nat) : BitVec 64 :=
  resFlag g (BitVec.ofNat 64 (c % resMod g)) ||| mask (anyPre c (4 * trialN w)) ||| evenFlag (c / 2) |||
    mask (anyPre (c / 2) (4 * trialN w))

theorem mask_eq_zero (b : Bool) : mask b = 0 ↔ b = false := by cases b <;> decide

theorem anyPre_mono {c m n : Nat} (h : m ≤ n) (hm : anyPre c m = true) : anyPre c n = true := by
  unfold anyPre at hm ⊢
  obtain ⟨i, hi, hp⟩ := List.any_eq_true.mp hm
  exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) h), hp⟩

/-- Above the table's largest prime, the sieve of `4 (trialN (mW bits))`
entries is `primeShape` and RSA's trial division for `bits`. -/
theorem sieved_sieve {bits c : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hc : 8161 < c) (ho : c % 2 = 1) :
    (primeShape c && !Spec.RsaKeyGen.obviouslyComposite bits c) = !anyPre c (4 * trialN (mW bits)) := by
  rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve hc ho]
  have ht : anyPre c (4 * trialN (mW bits)) = Spec.RsaKeyGen.obviouslyComposite bits c := by
    have e := VG.Proof.RsaKeyGen.trialAny_eq (w := mW bits) hc
    have e2 : Spec.RsaKeyGen.obviouslyComposite (64 * mW bits) c = Spec.RsaKeyGen.obviouslyComposite bits c := by
      unfold Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes
      have : (1024 < 64 * mW bits) = (1024 < bits) := propext (by simp only [mW]; omega)
      simp only [this]
    rw [← e2, ← e]
    rfl
  rw [← ht]
  have h53 : ((List.range 53).any fun i => c % tabEntry i == 0) = anyPre c 53 := rfl
  rw [h53]
  have hle : 53 ≤ 4 * trialN (mW bits) := by unfold trialN; split <;> omega
  cases h4 : anyPre c (4 * trialN (mW bits))
  · cases h5 : anyPre c 53
    · rfl
    · exact absurd (anyPre_mono hle h5) (by rw [h4]; decide)
  · cases anyPre c 53 <;> rfl

theorem shapeFlag_zero {bits g x : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : g = 2 ∨ g = 5) :
    shapeFlag g (mW bits) (candidateOf bits x) = 0 ↔
      (generationShape bits g (candidateOf bits x) && primeShape (candidateOf bits x) &&
        primeShape ((candidateOf bits x - 1) / 2) &&
        !Spec.RsaKeyGen.obviouslyComposite bits (candidateOf bits x) &&
        !Spec.RsaKeyGen.obviouslyComposite bits ((candidateOf bits x - 1) / 2)) = true := by
  obtain ⟨ho, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := bits) (by omega) x
  have hlen := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := bits) (by omega) x).1
  generalize candidateOf bits x = c at ho hl hlen ⊢
  have hbig : 2 ^ 14 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hq : (c - 1) / 2 = c / 2 := by omega
  rw [hq]
  have reorder (a b c d e : Bool) : (a && b && c && !d && !e) = (a && (b && !d) && (c && !e)) := by
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
  rw [reorder, sieved_sieve hb1 hb2 (by omega) ho]
  have hgen : generationShape bits g c = (if g = 2 then decide (c % 24 = 11) else
      decide (g = 5 ∧ (c % 10 = 3 ∨ c % 10 = 7))) := by
    unfold generationShape
    rcases hg with rfl | rfl <;> simp only [hb1, hb2, hlen, decide_true, beq_self_eq_true, Bool.and_true,
      Bool.true_and, ite_true, show ¬ (5 = 2) by decide, ite_false, true_and,
      Bool.decide_or, Nat.reduceBEq, Bool.false_eq_true] <;> simp only [trial_decide_beq]
  simp only [shapeFlag, VG.Proof.Rsa.AArch64.or_eq_zero, mask_eq_zero, evenFlag_zero, resFlag_zero hg]
  rw [hgen]
  rcases Nat.mod_two_eq_zero_or_one (c / 2) with hq2 | hq2
  · have hpq : primeShape (c / 2) = false := by
      unfold primeShape; simp [hq2]
    rw [hpq]
    simp only [hq2, Bool.false_and, Bool.and_false]
    simp
  · rw [sieved_sieve hb1 hb2 (by omega) hq2]
    rcases hg with rfl | rfl <;> simp [hq2]

end VG.Proof.Ffdh.AArch64.ParameterCandidate
