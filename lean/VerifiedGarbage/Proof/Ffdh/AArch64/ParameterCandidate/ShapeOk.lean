module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Halve
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Residue
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on AArch64: the shape's flag

`shapeFlag g c`, the value `fBad` ends with for the candidate `c`: zero
exactly when `c` has the generator's shape and `c` and `(c − 1) / 2` pass
`primeShape` (`shapeFlag_zero`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.Proof.Bignum VG.Proof.RsaKeyGen.AArch64 VG.Spec.Ffdh VG.Impl.RsaKeyGen

/-- The flag of the shape checks of `c`. -/
def shapeFlag (g c : Nat) : BitVec 64 :=
  resFlag g (BitVec.ofNat 64 (c % resMod g)) ||| mask (anyPre c 53) ||| evenFlag (c / 2) |||
    mask (anyPre (c / 2) 53)

theorem mask_eq_zero (b : Bool) : mask b = 0 ↔ b = false := by cases b <;> decide

theorem shapeFlag_zero {bits g x : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : g = 2 ∨ g = 5) :
    shapeFlag g (candidateOf bits x) = 0 ↔
      (generationShape bits g (candidateOf bits x) && primeShape (candidateOf bits x) &&
        primeShape ((candidateOf bits x - 1) / 2)) = true := by
  obtain ⟨ho, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := bits) (by omega) x
  have hlen := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := bits) (by omega) x).1
  generalize candidateOf bits x = c at ho hl hlen ⊢
  have hbig : 2 ^ 14 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hq : (c - 1) / 2 = c / 2 := by omega
  rw [hq]
  have hp := VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve (p := c) (by omega) ho
  have hgen : generationShape bits g c = (if g = 2 then decide (c % 24 = 11) else
      decide (g = 5 ∧ (c % 10 = 3 ∨ c % 10 = 7))) := by
    unfold generationShape
    rcases hg with rfl | rfl <;> simp only [hb1, hb2, hlen, decide_true, beq_self_eq_true, Bool.and_true,
      Bool.true_and, ite_true, show ¬ (5 = 2) by decide, ite_false, true_and,
      Bool.decide_or, Nat.reduceBEq, Bool.false_eq_true] <;> simp only [trial_decide_beq]
  simp only [shapeFlag, VG.Proof.Rsa.AArch64.or_eq_zero, mask_eq_zero, evenFlag_zero, resFlag_zero hg]
  rw [hgen, hp]
  rcases Nat.mod_two_eq_zero_or_one (c / 2) with hq2 | hq2
  · have hpq : primeShape (c / 2) = false := by
      unfold primeShape; simp [hq2]
    rw [hpq]
    simp only [hq2, Bool.and_false]
    simp
  · rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve (p := c / 2) (by omega) hq2]
    rcases hg with rfl | rfl <;> simp [anyPre, hq2]

end VG.Proof.Ffdh.AArch64.ParameterCandidate
