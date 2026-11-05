module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Impl.RsaKeyGen.Primes
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter

/-!
# An FFDH parameter candidate on PPC64LE: its shape

`shape_iff`: the flags of the congruence, the sieves of p and q and q's
parity are all clear exactly when the specification's shape checks pass.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.Impl.MillerRabin.PPC64LE.Search

theorem oddPrimes_eq : oddPrimes256 = (List.range 53).map VG.Impl.RsaKeyGen.tabEntry := by
  unfold VG.Impl.RsaKeyGen.tabEntry VG.Impl.RsaKeyGen.slots
  rw [VG.Impl.RsaKeyGen.primes.lit_eq]
  decide +kernel

theorem noDiv_iff (x : Nat) :
    (∀ d ∈ oddPrimes256, x % d ≠ 0) ↔ ((List.range 53).any fun i => x % VG.Impl.RsaKeyGen.tabEntry i == 0) = false := by
  rw [oddPrimes_eq, List.any_eq_false]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, beq_iff_eq]

theorem shape_iff {bits g x : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : g = 2 ∨ g = 5) :
    (goodRes g (Spec.Ffdh.candidateOf bits x) ∧ (∀ d ∈ oddPrimes256, Spec.Ffdh.candidateOf bits x % d ≠ 0) ∧
        Spec.Ffdh.candidateOf bits x / 2 % 2 = 1 ∧ ∀ d ∈ oddPrimes256, Spec.Ffdh.candidateOf bits x / 2 % d ≠ 0) ↔
      (Spec.Ffdh.generationShape bits g (Spec.Ffdh.candidateOf bits x) &&
        Spec.Ffdh.primeShape (Spec.Ffdh.candidateOf bits x) &&
        Spec.Ffdh.primeShape ((Spec.Ffdh.candidateOf bits x - 1) / 2)) = true := by
  obtain ⟨ho, hl, hu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := bits) (by omega_arith) x
  have hbl := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := bits) (by omega_arith) x).1
  obtain ⟨hql, _⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) ho hl hu
  generalize Spec.Ffdh.candidateOf bits x = c at ho hl hu hbl hql ⊢
  have hq : (c - 1) / 2 = c / 2 := by omega_arith
  have big : 8161 < c := Nat.lt_of_lt_of_le (by decide : 8161 < 2 ^ 13)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith : 13 ≤ bits - 1)) hl)
  have bigq : 8161 < c / 2 := by
    rw [← hq]
    exact Nat.lt_of_lt_of_le (by decide : 8161 < 2 ^ 13)
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith : 13 ≤ bits - 2)) hql)
  have hgen : Spec.Ffdh.generationShape bits g c = true ↔ goodRes g c := by
    unfold Spec.Ffdh.generationShape goodRes
    rcases hg with rfl | rfl <;> simp [hb1, hb2, hbl]
  have hp := VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve big ho
  rw [hq]
  simp only [Bool.and_eq_true, hgen, hp, Bool.not_eq_eq_eq_not, Bool.not_true, ← noDiv_iff c]
  by_cases hqo : c / 2 % 2 = 1
  · rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve bigq hqo]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, ← noDiv_iff (c / 2), hqo, true_and, and_assoc]
  · have hf : Spec.Ffdh.primeShape (c / 2) = false := by
      unfold Spec.Ffdh.primeShape; simp [hqo]
    rw [hf]
    simp [hqo]

/-- The entries of RSA's table trial division uses for a candidate of
`bits` bits: 512, or 1024 above 1024 bits. -/
def trialN (bits : Nat) : Nat := if (bits + 63) / 64 ≤ 16 then 512 else 1024

/-- Trial division by them is `obviouslyComposite` for `bits`. -/
theorem trialN_spec {bits c : Nat} (large : 8161 < c) :
    VG.Proof.RsaKeyGen.trialPrefix c (trialN bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
  unfold trialN
  rw [VG.Proof.RsaKeyGen.trialPrefix_spec large]
  unfold Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes
  have : (1024 < 64 * ((bits + 63) / 64)) = (1024 < bits) := propext (by omega)
  simp only [this]

/-- The shape's flags, and trial division of p and q, all clear exactly when
the sieved specification's shape checks pass. -/
theorem sieved_shape_iff {bits g x : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : g = 2 ∨ g = 5) :
    (goodRes g (Spec.Ffdh.candidateOf bits x) ∧ (∀ d ∈ oddPrimes256, Spec.Ffdh.candidateOf bits x % d ≠ 0) ∧
        VG.Proof.RsaKeyGen.trialPrefix (Spec.Ffdh.candidateOf bits x) (trialN bits) = false ∧
        Spec.Ffdh.candidateOf bits x / 2 % 2 = 1 ∧ (∀ d ∈ oddPrimes256, Spec.Ffdh.candidateOf bits x / 2 % d ≠ 0) ∧
        VG.Proof.RsaKeyGen.trialPrefix (Spec.Ffdh.candidateOf bits x / 2) (trialN bits) = false) ↔
      (Spec.Ffdh.generationShape bits g (Spec.Ffdh.candidateOf bits x) &&
        Spec.Ffdh.primeShape (Spec.Ffdh.candidateOf bits x) &&
        Spec.Ffdh.primeShape ((Spec.Ffdh.candidateOf bits x - 1) / 2) &&
        !Spec.RsaKeyGen.obviouslyComposite bits (Spec.Ffdh.candidateOf bits x) &&
        !Spec.RsaKeyGen.obviouslyComposite bits ((Spec.Ffdh.candidateOf bits x - 1) / 2)) = true := by
  have hs := shape_iff (x := x) hb1 hb2 hg
  obtain ⟨ho, hl, hu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := bits) (by omega_arith) x
  obtain ⟨hql, _⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) ho hl hu
  generalize Spec.Ffdh.candidateOf bits x = c at hs ho hl hu hql ⊢
  have hq : (c - 1) / 2 = c / 2 := by omega_arith
  have big : 8161 < c := Nat.lt_of_lt_of_le (by decide : 8161 < 2 ^ 13)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith : 13 ≤ bits - 1)) hl)
  have bigq : 8161 < c / 2 := by
    rw [← hq]
    exact Nat.lt_of_lt_of_le (by decide : 8161 < 2 ^ 13)
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith : 13 ≤ bits - 2)) hql)
  rw [trialN_spec big, trialN_spec bigq, ← hq]
  rw [hq] at hs
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hs ⊢
  rw [hq]
  constructor
  · rintro ⟨a, b, c', d, e, f⟩
    exact ⟨⟨hs.mp ⟨a, b, d, e⟩, c'⟩, f⟩
  · rintro ⟨⟨h1, c'⟩, f⟩
    obtain ⟨a, b, d, e⟩ := hs.mpr h1
    exact ⟨a, b, c', d, e, f⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
