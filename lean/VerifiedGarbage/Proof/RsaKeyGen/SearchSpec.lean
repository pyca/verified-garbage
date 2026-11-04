module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: it names no ISA, for every target's prime search

/-! # The RSA prime search's specification: what every target's proof uses

A candidate leaves a suffix of its tape (`candidateOp_suffix`), so the search
from an offset into one tape (`primeTail`) steps by unfolding `primeSearch`
once: each candidate's outcome, the octets it consumed, and the search from
the offset after them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Search

open VG VG.Spec.RsaKeyGen

/-! ## Candidates consume a prefix -/

theorem draw_suffix {n : Nat} {r : Rand} {x : Nat} {rest : Rand} (h : draw n r = some (x, rest)) :
    rest = r.drop n ∧ n ≤ r.length := by
  unfold draw at h
  simp only at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, by rw [List.length_take] at hl; omega⟩
  · cases h

theorem loop_suffix {σ α : Type} {step : σ → Rand → Option ((α ⊕ σ) × Rand)}
    (hstep : ∀ s r x r', step s r = some (x, r') → ∃ n ≤ r.length, r' = r.drop n) :
    ∀ s r a r', loop step s r = some (a, r') → ∃ n ≤ r.length, r' = r.drop n := by
  intro s r
  induction r using (measure List.length).wf.induction generalizing s with
  | h r ih =>
    intro a r' h
    rw [loop] at h
    split at h
    · cases h
    · cases h
      exact hstep _ _ _ _ (by assumption)
    · rename_i s' r₁ hs
      split at h
      · rename_i hlt
        obtain ⟨n, hn, rfl⟩ := hstep _ _ _ _ hs
        obtain ⟨m, hm, rfl⟩ := ih _ hlt _ _ _ h
        refine ⟨n + m, ?_, by rw [List.drop_drop]⟩
        rw [List.length_drop] at hm
        omega
      · cases h

theorem mrStep_suffix {w ch a m : Nat} :
    ∀ (s : Nat × Nat) (r : Rand) x r', mrStep w ch a m s r = some (x, r') → ∃ n ≤ r.length, r' = r.drop n := by
  intro s r x r' hs
  obtain ⟨i, u⟩ := s
  unfold mrStep at hs
  simp only at hs
  split at hs
  · rcases hd : draw (witnessBytes w) r with _ | ⟨y, r₁⟩
    · simp [hd] at hs
    · simp only [hd, Option.bind_eq_bind, Option.bind_some] at hs
      obtain ⟨hr₁, hn⟩ := draw_suffix hd
      split at hs <;>
        (simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hs
         exact ⟨_, hn, hs.2.symm.trans hr₁⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs
    exact ⟨0, Nat.zero_le _, by rw [List.drop_zero]; exact hs.2.symm⟩

theorem primalityTest_suffix {w : Nat} {r : Rand} {b : Bool} {rest : Rand}
    (h : primalityTest w r = some (b, rest)) : ∃ n ≤ r.length, rest = r.drop n := by
  have h0 : ∀ {x : Bool}, some (x, r) = some (b, rest) → ∃ n ≤ r.length, rest = r.drop n :=
    fun hx => ⟨0, Nat.zero_le _, by rw [List.drop_zero]; exact (Prod.mk.inj (Option.some.inj hx)).2.symm⟩
  unfold primalityTest at h
  split at h
  · exact h0 h
  split at h
  · exact h0 h
  split at h
  · exact h0 h
  exact loop_suffix mrStep_suffix _ _ _ _ h

/-- A candidate leaves a suffix of its tape, after at least its own octets. -/
theorem candidateOp_suffix {L : Nat} {eB pB r : Rand} {x : Candidate} {rest : Rand}
    (h : candidateOp L eB pB r = some (x, rest)) : ∃ n ≤ r.length, L ≤ n ∧ rest = r.drop n := by
  unfold candidateOp candidateStep at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨y, r₁⟩, hd, h⟩ := h
  obtain ⟨hr₁, hn⟩ := draw_suffix hd
  have hL : 8 * L / 8 = L := by omega
  rw [hL] at hr₁ hn
  dsimp only at h
  split at h
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨L, hn, Nat.le_refl _, h.2.symm.trans hr₁⟩
  · split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨b, r₂⟩, ht, h⟩ := h
      obtain ⟨m, hm, rfl⟩ := primalityTest_suffix ht
      have hrest : rest = r₁.drop m := by
        split at h <;> (simp only [pure, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)
      refine ⟨L + m, ?_, by omega, by rw [hrest, hr₁, List.drop_drop]⟩
      rw [hr₁, List.length_drop] at hm
      omega
    · simp only [Option.bind_some] at h
      have hrest : rest = r₁ := by
        split at h <;> (simp only [pure, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)
      exact ⟨L, hn, Nat.le_refl _, hrest.trans hr₁⟩

/-- A candidate too close to the other prime consumes exactly its own octets. -/
theorem candidateOp_close {L : Nat} {eB pB r : Rand} {rest : Rand}
    (h : candidateOp L eB pB r = some (.close, rest)) : rest = r.drop L ∧ L ≤ r.length := by
  unfold candidateOp candidateStep at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨y, r₁⟩, hd, h⟩ := h
  obtain ⟨hr₁, hn⟩ := draw_suffix hd
  have hL : 8 * L / 8 = L := by omega
  rw [hL] at hr₁ hn
  dsimp only at h
  split at h
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm.trans hr₁, hn⟩
  · split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨b, r₂⟩, _, h⟩ := h
      split at h <;> (simp only [pure, Option.some.injEq, Prod.mk.injEq] at h; cases h.1)
    · simp only [Option.bind_some] at h
      split at h <;> (simp only [pure, Option.some.injEq, Prod.mk.injEq] at h; cases h.1)

/-! ## The search, one candidate at a time -/

/-- A candidate's entry in the trace: its leak, after its length. -/
abbrev entry (L : Nat) (eB pB r : Rand) : List Nat :=
  (candidateLeak L eB pB r).length :: candidateLeak L eB pB r

variable {L : Nat} {eB pB : Rand} {remaining : Nat}

theorem search_zero (r : Rand) : primeSearch L eB pB 0 r = ⟨.exhausted, 0, []⟩ := by
  rw [primeSearch]; rfl

theorem search_short {remaining : Nat} {r : Rand} (hr : remaining ≠ 0)
    (hc : candidateOp L eB pB r = none) :
    primeSearch L eB pB remaining r =
      if primeEntropy L ≤ r.length then ⟨.exhausted, 0, entry L eB pB r⟩
      else ⟨.entropy remaining (primeRequest L r.length), 0, entry L eB pB r⟩ := by
  rw [primeSearch, ite_eq_right_of_eq_false _ _ (eq_false hr)]
  simp only [hc]

theorem search_prime {remaining : Nat} {r rest : Rand} {c : Nat} (hr : remaining ≠ 0)
    (hc : candidateOp L eB pB r = some (.prime c, rest)) :
    primeSearch L eB pB remaining r = ⟨.accepted c, r.length - rest.length, entry L eB pB r⟩ := by
  rw [primeSearch, ite_eq_right_of_eq_false _ _ (eq_false hr)]
  simp only [hc]

theorem search_close {remaining : Nat} {r rest : Rand} (hr : remaining ≠ 0)
    (hc : candidateOp L eB pB r = some (.close, rest)) :
    primeSearch L eB pB remaining r =
      if rest.length < r.length then
        (primeSearch L eB pB remaining rest).consume (r.length - rest.length) (entry L eB pB r)
      else ⟨.exhausted, 0, entry L eB pB r⟩ := by
  rw [primeSearch, ite_eq_right_of_eq_false _ _ (eq_false hr)]
  simp only [hc]
  split <;> rfl

theorem search_rejected {remaining : Nat} {r rest : Rand} (hr : remaining ≠ 0)
    (hc : candidateOp L eB pB r = some (.rejected, rest)) :
    primeSearch L eB pB remaining r =
      if rest.length < r.length then
        (primeSearch L eB pB (remaining - 1) rest).consume (r.length - rest.length) (entry L eB pB r)
      else ⟨.exhausted, 0, entry L eB pB r⟩ := by
  rw [primeSearch, ite_eq_right_of_eq_false _ _ (eq_false hr)]
  simp only [hc]
  split <;> rfl

theorem consume_consume (r : PrimeSearchResult) (a b : Nat) (x y : List Nat) :
    (r.consume b y).consume a x = r.consume (a + b) (x ++ y) := by
  simp only [Spec.Entropy.Result.consume, Nat.add_assoc, List.append_assoc]

/-! ## What the trace says -/

/-- With candidates left, the trace starts with the next candidate's entry. -/
theorem search_trace (hr : remaining ≠ 0) (r : Rand) :
    ∃ rest, (primeSearch L eB pB remaining r).trace = entry L eB pB r ++ rest := by
  rw [primeSearch, ite_eq_right_of_eq_false _ _ (eq_false hr)]
  simp only
  split
  · split <;> exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨[], by simp⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨[], by simp⟩

/-- A candidate's status, from its leak. -/
def statusOfLeak : List Nat → Nat
  | s :: _ => s
  | [] => 0

/-- The octets a candidate consumed, from its leak and the prime's width. -/
def usedOfLeak (L : Nat) : List Nat → Nat
  | [1, n] => n
  | [2] => L
  | 3 :: bs => bs.length
  | _ => 0

theorem status_of_leak (r : Rand) :
    candidateStatus (candidateOp L eB pB r) = statusOfLeak (candidateLeak L eB pB r) := by
  cases hc : candidateOp L eB pB r with
  | none => simp [candidateLeak, candidateStatus, hc, statusOfLeak]
  | some pr =>
    obtain ⟨x, rest⟩ := pr
    cases x <;> simp [candidateLeak, candidateStatus, hc, statusOfLeak]

theorem used_of_leak (r : Rand) :
    (match candidateOp L eB pB r with
      | some (_, rest) => r.length - rest.length
      | none => 0) = usedOfLeak L (candidateLeak L eB pB r) := by
  cases hc : candidateOp L eB pB r with
  | none => simp [candidateLeak, hc, usedOfLeak]
  | some pr =>
    obtain ⟨x, rest⟩ := pr
    cases x with
    | prime c => simp [candidateLeak, hc, usedOfLeak]
    | close =>
      obtain ⟨hd, hL⟩ := candidateOp_close hc
      simp only [candidateLeak, hc, usedOfLeak, hd, List.length_drop]
      omega
    | rejected =>
      obtain ⟨n, hn, -, hd⟩ := candidateOp_suffix hc
      simp only [candidateLeak, hc, usedOfLeak, List.length_map, List.length_take, hd, List.length_drop]
      omega

/-- Two traces that agree start with the same entry. -/
theorem entry_eq {l₁ l₂ r₁ r₂ : List Nat} (h : (l₁.length :: l₁) ++ r₁ = (l₂.length :: l₂) ++ r₂) :
    l₁ = l₂ := by
  simp only [List.cons_append, List.cons.injEq] at h
  obtain ⟨hl, h⟩ := h
  have := congrArg (List.take l₁.length) h
  rwa [List.take_left' rfl, hl, List.take_left' rfl] at this

end VG.Proof.RsaKeyGen.Search
