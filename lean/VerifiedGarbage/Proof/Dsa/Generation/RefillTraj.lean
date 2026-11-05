module

public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: target-independent facts about the spec, for the controllers of every target's search

/-! # The refillable-tape parameter search, seed by seed from the start

A native controller runs seeds over the tape `R` from `left` seeds left and
the cursor 0: `step` is one of its iterations (the next seed's position, or
the same once the search stops), `pos i` its position after `i` of them, and
`iters k c` how many it runs from `(k, c)`, the last included. The whole
search's result, from the cursor `c` with `k` seeds left, is the same at
every position the controller reaches (`res_step`), so at the end it is the
result of the last iteration's case (`RefillSearch.lean`). -/

@[expose] public section

namespace VG.Proof.Dsa.Generation

open VG Spec.Dsa

section
variable (pLen : Nat) (R : List Byte)

/-- The seed at the cursor `c`. -/
abbrev attemptAt (c : Nat) : Option (Option Params × List Byte) :=
  refillAttempt pLen (generationQLen pLen) ((R.drop c).take (generationQLen pLen))
    (R.drop (c + generationQLen pLen))

/-- The iterations a controller runs from `k` seeds left and the cursor `c`. -/
def iters : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, c =>
    if R.length - c < generationQLen pLen then 1 else
      match attemptAt pLen R c with
      | some (none, r) => iters k (R.length - r.length) + 1
      | _ => 1

/-- One iteration: the next seed's position if this one is rejected. -/
def step : Nat × Nat → Nat × Nat
  | (0, c) => (0, c)
  | (k + 1, c) =>
    if R.length - c < generationQLen pLen then (k + 1, c) else
      match attemptAt pLen R c with
      | some (none, r) => (k, R.length - r.length)
      | _ => (k + 1, c)

/-- The position after `i` iterations from `left` seeds and the cursor 0. -/
def pos (left : Nat) : Nat → Nat × Nat
  | 0 => (left, 0)
  | i + 1 => step pLen R (pos left i)

/-- The search's result from a position, with what came before consumed. -/
abbrev resAt (p : Nat × Nat) : ParameterSearchResult := (parameterSearch pLen p.1 (R.drop p.2)).consume p.2 []

end

theorem iters_pos (pLen : Nat) (R : List Byte) (k c : Nat) : 0 < iters pLen R k c := by
  cases k with
  | zero => simp [iters]
  | succ k =>
    simp only [iters]
    split
    · omega
    · split <;> omega

/-- A rejected seed's rest is the tape after a cursor. -/
theorem rest_drop {pLen c : Nat} {R r : List Byte} {x : Option Params}
    (hc : c + generationQLen pLen ≤ R.length) (h : attemptAt pLen R c = some (x, r)) :
    r = R.drop (R.length - r.length) ∧ c + generationQLen pLen ≤ R.length - r.length := by
  have hs := refillAttempt_suffix h
  obtain ⟨p, hp⟩ := hs
  have hl : (R.drop (c + generationQLen pLen)).length = p.length + r.length := by rw [← hp, List.length_append]
  have hl' : R.length - (c + generationQLen pLen) = p.length + r.length := by rwa [List.length_drop] at hl
  have hR : R.length = (c + generationQLen pLen) + (p.length + r.length) := by rw [← hl']; omega
  have hr : R.length - r.length = c + generationQLen pLen + p.length := by rw [hR]; omega
  refine ⟨?_, by rw [hr]; omega⟩
  have e : R.drop (c + generationQLen pLen) = p ++ r := hp.symm
  have : R.drop (c + generationQLen pLen + p.length) = r := by
    rw [← List.drop_drop, e, List.drop_left]
  rw [hr]; exact this.symm

/-- From a position with more than one iteration left, the next has one fewer. -/
theorem iters_step {pLen : Nat} {R : List Byte} {k c n : Nat} (h : iters pLen R k c = n + 1) (hn : 0 < n) :
    iters pLen R (step pLen R (k, c)).1 (step pLen R (k, c)).2 = n := by
  cases k with
  | zero => simp [iters] at h; omega
  | succ k =>
    simp only [iters] at h
    simp only [step]
    by_cases hs : R.length - c < generationQLen pLen
    · simp only [hs, ↓reduceIte] at h; omega
    · simp only [hs, ↓reduceIte] at h ⊢
      rcases e : attemptAt pLen R c with _ | ⟨_ | _, r⟩ <;> simp only [e] at h ⊢ <;> omega

/-- The cursor stays within the tape. -/
theorem step_le {pLen : Nat} {R : List Byte} {k c : Nat} (hc : c ≤ R.length) :
    (step pLen R (k, c)).2 ≤ R.length := by
  cases k with
  | zero => simpa [step]
  | succ k =>
    simp only [step]
    split
    · exact hc
    · split
      · simp
      · exact hc

/-- The search's result is the same at the next position. -/
theorem res_step {pLen : Nat} (hw : 0 < pLen) {R : List Byte} {k c : Nat} (hc : c ≤ R.length) :
    resAt pLen R (step pLen R (k, c)) = resAt pLen R (k, c) := by
  cases k with
  | zero => simp [step]
  | succ k =>
    simp only [step]
    split
    · rfl
    · rename_i hs
      have hcq : c + generationQLen pLen ≤ R.length := by omega
      split
      · rename_i r e
        obtain ⟨hr, hu⟩ := rest_drop hcq e
        rw [hr] at e
        exact (search_rejected hw hcq (by omega) e).symm
      · rfl

/-- The positions' cursors are within the tape. -/
theorem pos_le (pLen : Nat) (R : List Byte) (left : Nat) : ∀ i, (pos pLen R left i).2 ≤ R.length
  | 0 => by simp [pos]
  | i + 1 => by
    simp only [pos]
    exact step_le (pos_le pLen R left i)

/-- The result at every position is the whole search's. -/
theorem res_pos {pLen : Nat} (hw : 0 < pLen) (R : List Byte) (left : Nat) :
    ∀ i, resAt pLen R (pos pLen R left i) = parameterSearch pLen left R
  | 0 => by simp [pos, resAt, Spec.Entropy.Result.consume]
  | i + 1 => by
    simp only [pos]
    have := pos_le pLen R left i
    rw [res_step hw this]
    exact res_pos hw R left i

/-- The iterations left at the `i`-th position. -/
theorem iters_at {pLen : Nat} {R : List Byte} {left : Nat} :
    ∀ i < iters pLen R left 0, iters pLen R (pos pLen R left i).1 (pos pLen R left i).2 = iters pLen R left 0 - i
  | 0, _ => by simp [pos]
  | i + 1, hi => by
    have ih := iters_at (pLen := pLen) (R := R) (left := left) i (by omega)
    simp only [pos]
    have := iters_step (pLen := pLen) (R := R) (k := (pos pLen R left i).1) (c := (pos pLen R left i).2)
      (n := iters pLen R left 0 - i - 1) (by rw [ih]; omega) (by omega)
    rw [this]; omega

/-- The status a controller's iteration at a position ends with: 3 for no
seeds left, 0 for a tape too short or a seed that ran out, 2 for a rejected
seed and 1 for parameters. -/
def stAt (pLen : Nat) (R : List Byte) : Nat × Nat → Nat
  | (0, _) => 3
  | (_ + 1, c) =>
    if R.length - c < generationQLen pLen then 0 else
      match attemptAt pLen R c with
      | some (none, _) => 2
      | some (some _, _) => 1
      | none => 0

/-- The last iteration does not reject. -/
theorem stAt_last {pLen : Nat} {R : List Byte} {k c : Nat} (h : iters pLen R k c = 1) : stAt pLen R (k, c) ≠ 2 := by
  cases k with
  | zero => simp [stAt]
  | succ k =>
    simp only [iters] at h
    simp only [stAt]
    by_cases hs : R.length - c < generationQLen pLen
    · simp [hs]
    · simp only [hs, ↓reduceIte] at h ⊢
      rcases e : attemptAt pLen R c with _ | ⟨_ | _, r⟩ <;> simp only [e] at h ⊢
      · decide
      · have := iters_pos pLen R k (R.length - r.length); omega
      · decide

/-- Any other rejects. -/
theorem stAt_more {pLen : Nat} {R : List Byte} {k c : Nat} (h : 1 < iters pLen R k c) : stAt pLen R (k, c) = 2 := by
  cases k with
  | zero => simp [iters] at h
  | succ k =>
    simp only [iters] at h
    simp only [stAt]
    by_cases hs : R.length - c < generationQLen pLen
    · simp only [hs, ↓reduceIte] at h; omega
    · simp only [hs, ↓reduceIte] at h ⊢
      rcases e : attemptAt pLen R c with _ | ⟨_ | _, r⟩ <;> simp only [e] at h ⊢ <;> omega

theorem step_fst_le (pLen : Nat) (R : List Byte) (p : Nat × Nat) : (step pLen R p).1 ≤ p.1 := by
  obtain ⟨k, c⟩ := p
  cases k with
  | zero => simp [step]
  | succ k =>
    simp only [step]
    split
    · simp
    · split <;> simp

/-- The seeds left never grow. -/
theorem pos_fst_le (pLen : Nat) (R : List Byte) (left : Nat) : ∀ i, (pos pLen R left i).1 ≤ left
  | 0 => by simp [pos]
  | i + 1 => by
    simp only [pos]
    exact Nat.le_trans (step_fst_le pLen R _) (pos_fst_le pLen R left i)

theorem stAt_le (pLen : Nat) (R : List Byte) (p : Nat × Nat) : stAt pLen R p ≤ 3 := by
  obtain ⟨k, c⟩ := p
  cases k with
  | zero => simp [stAt]
  | succ k =>
    simp only [stAt]
    split
    · omega
    · split <;> omega

end VG.Proof.Dsa.Generation
