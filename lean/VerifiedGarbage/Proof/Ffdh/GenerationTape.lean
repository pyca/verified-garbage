module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Framework.Omega

/-! # Complete generation consumes prefixes, including every rejected witness -/

@[expose] public section

namespace VG.Proof.Ffdh.Generation

open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen VG.Proof.Ffdh.ParameterCandidate

theorem checkWitnesses_suffix {w : Nat} (hn : 0 < witnessOctets w) :
    ∀ n r pass rest, checkWitnesses w n r = some (pass, rest) →
      ∃ used ≤ r.length, rest = r.drop used := by
  intro n
  induction n with
  | zero =>
    intro r pass rest he
    simp only [checkWitnesses, Option.some.injEq, Prod.mk.injEq] at he
    exact ⟨0, Nat.zero_le _, by simpa only [List.drop_zero] using he.2.symm⟩
  | succ n ih =>
    intro r pass rest he
    simp only [checkWitnesses, bind, Option.bind_eq_some_iff] at he
    obtain ⟨⟨a, r'⟩, ha, he⟩ := he
    obtain ⟨used, _, hu, hr⟩ := drawWitness_suffix hn r a r' ha
    dsimp only at he
    split at he
    · obtain ⟨more, hm, ht⟩ := ih _ _ _ he
      refine ⟨used + more, ?_, ?_⟩
      · rw [hr, List.length_drop] at hm
        omega_using [hm, hu]
      · rw [ht, hr, List.drop_drop]
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨used, hu, he.2.symm.trans hr⟩

private theorem witness_width_pos {w : Nat} (hs : primeShape w = true) :
    0 < witnessOctets w := by
  have hw : 2 < w := by
    simp only [primeShape, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact hs.1.1
  have hn : w - 1 ≠ 0 := by omega_using [hw]
  simp only [witnessOctets, bitLength, hn, ite_false]
  omega

theorem candidate_suffix {bits generator : Nat} {r rest : Rand} {p : Option Nat}
    (he : parameterCandidate bits generator r = some (p, rest)) :
    ∃ used ≤ r.length, rest = r.drop used := by
  rw [← checkedCandidate_eq] at he
  unfold checkedCandidate at he
  simp only [bind, Option.bind_eq_some_iff] at he
  obtain ⟨⟨x, r'⟩, hd, he⟩ := he
  have hlen : (bits + 7) / 8 ≤ r.length := by
    by_cases h : (bits + 7) / 8 ≤ r.length
    · exact h
    · rw [draw_of_short (by omega_using [h] : r.length < (bits + 7) / 8)] at hd
      cases hd
  rw [draw_of_le hlen] at hd
  obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp (Option.some.inj hd)
  dsimp only at he
  split at he
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
    exact ⟨(bits + 7) / 8, hlen, he.2.symm⟩
  · rename_i hs
    have hshape : (generationShape bits generator (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
        primeShape (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
        primeShape ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2)) = true := by
      have hn := Bool.eq_false_iff.mpr hs
      simpa only [Bool.not_eq_false'] using hn
    have hq := witness_width_pos ((Bool.and_eq_true _ _).mp hshape).2
    have hp := witness_width_pos ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hshape).1).2
    simp only [Option.bind_eq_some_iff] at he
    obtain ⟨⟨passq, rq⟩, hqrun, he⟩ := he
    obtain ⟨uq, huq, hrq⟩ := checkWitnesses_suffix hq _ _ _ _ hqrun
    dsimp only at he
    split at he
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
      refine ⟨(bits + 7) / 8 + uq, ?_, ?_⟩
      · rw [List.length_drop] at huq
        omega_using [hlen, huq]
      · rw [he.2.symm, hrq, List.drop_drop]
    · simp only [Option.bind_eq_some_iff] at he
      obtain ⟨⟨passp, rp⟩, hprun, he⟩ := he
      obtain ⟨up, hup, hrp⟩ := checkWitnesses_suffix hp _ _ _ _ hprun
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
      refine ⟨(bits + 7) / 8 + uq + up, ?_, ?_⟩
      · rw [hrq, List.length_drop, List.length_drop] at hup
        rw [List.length_drop] at huq
        omega_using [hlen, huq, hup]
      · rw [he.2.symm, hrp, hrq, List.drop_drop, List.drop_drop, Nat.add_assoc]

end VG.Proof.Ffdh.Generation
