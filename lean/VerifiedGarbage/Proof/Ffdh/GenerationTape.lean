module

public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Framework.Omega

/-! # A witness batch consumes a prefix of the tape, including every rejected witness -/

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

end VG.Proof.Ffdh.Generation
