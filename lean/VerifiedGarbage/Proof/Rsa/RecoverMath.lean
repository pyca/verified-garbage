import VerifiedGarbage.Proof.Rsa.KeyMath

/-!
# Recovering the prime factors: the mathematics

Target-independent models, on naturals, of what the code of
`vg_rsa_recover_primes` computes with a fixed number of steps, and their
relation to the specification (`Spec.Rsa.recoverPrimes`):

* Halvings of `m`, each only if `m` is even, counting them
  (`halveStep`): as many as `m` has bits leave `splitTwos m` (`halve_iter`).
* Squarings under masks (`sqStep`): from `y = g^r mod n`, done if `y = ±1`,
  each live squaring (not done, and fewer than `t`) finds `y` if `y² = 1`,
  stops if `y² = -1` or it is the `t`-th, and continues with `y := y²`
  otherwise; after at least `t` of them, `ok` and `y` are
  `recoverStep`'s result (`sq_result`).
* The candidates `g = 2, 3, …` until one gives a result or 100 are tried
  (`go_found`, `go_none`).
-/

namespace VG.Proof.Rsa

open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries powMod)

/-! ## Halvings -/

/-- `(m, t) ↦ (m / 2, t + 1)` if `m` is even. -/
def halveStep (st : Nat × Nat) : Nat × Nat := if st.1 % 2 = 0 then (st.1 / 2, st.2 + 1) else st

theorem splitTwos_odd {m : Nat} (h : m % 2 = 1) : splitTwos m = (0, m) := by
  rw [Spec.Rsa.splitTwos.eq_1]; simp [h]

theorem splitTwos_even {m : Nat} (h0 : m ≠ 0) (h : m % 2 = 0) :
    splitTwos m = ((splitTwos (m / 2)).1 + 1, (splitTwos (m / 2)).2) := by
  have h' : ¬ (m = 0 ∨ m % 2 = 1) := by omega
  rw [Spec.Rsa.splitTwos.eq_1]; simp only [h', ite_false]

/-- `m = 2^t r` with `r` odd. -/
theorem splitTwos_spec {m : Nat} (hm : 0 < m) :
    m = 2 ^ (splitTwos m).1 * (splitTwos m).2 ∧ (splitTwos m).2 % 2 = 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · obtain ⟨e1, e2⟩ := ih (m / 2) (by omega) (by omega)
      rw [splitTwos_even (by omega) h]
      refine ⟨?_, e2⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ _) 2, Nat.mul_assoc, ← e1]
      omega
    · rw [splitTwos_odd h]
      exact ⟨by simp, h⟩

theorem splitTwos_lt {m K : Nat} (hm : 0 < m) (hK : m < 2 ^ K) : (splitTwos m).1 < K := by
  obtain ⟨e1, e2⟩ := splitTwos_spec hm
  have h1 : 2 ^ (splitTwos m).1 ≤ m :=
    calc 2 ^ (splitTwos m).1 ≤ 2 ^ (splitTwos m).1 * (splitTwos m).2 := Nat.le_mul_of_pos_right _ (by omega)
      _ = m := e1.symm
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt h1 hK)

/-- At least `t` halvings of `m = 2^t r` leave `(r, s + t)`. -/
theorem halve_iter {m : Nat} (hm : 0 < m) {K : Nat} (hK : (splitTwos m).1 ≤ K) (s : Nat) :
    halveStep^[K] (m, s) = ((splitTwos m).2, s + (splitTwos m).1) := by
  induction K generalizing m s with
  | zero =>
    have h0 : (splitTwos m).1 = 0 := by omega
    have hodd : m % 2 = 1 := by
      have := (splitTwos_spec hm).1; rw [h0, Nat.pow_zero, Nat.one_mul] at this
      have := (splitTwos_spec hm).2; omega
    rw [splitTwos_odd hodd]; rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have e := splitTwos_even (by omega) h
      have hs : halveStep (m, s) = (m / 2, s + 1) := by simp [halveStep, h]
      rw [hs, ih (by omega) (by rw [e] at hK; dsimp only at hK; omega), e]
      simp only [Prod.mk.injEq, true_and]
      omega
    · have hs : halveStep (m, s) = (m, s) := by simp [halveStep, h]
      rw [hs, ih hm (by rw [splitTwos_odd h]; exact Nat.zero_le _), splitTwos_odd h]

/-- `K` halvings of `0 < m < 2^K`, from `t = 0`: `splitTwos m`, swapped. -/
theorem halve_done {m K : Nat} (hm : 0 < m) (hK : m < 2 ^ K) :
    halveStep^[K] (m, 0) = ((splitTwos m).2, (splitTwos m).1) := by
  rw [halve_iter hm (Nat.le_of_lt (splitTwos_lt hm hK)), Nat.zero_add]

/-! ## Squarings -/

/-- A squaring under masks, the `k`-th (from 0) of a candidate whose `m`
has `t` factors 2: `(y, done, ok)`. -/
def sqStep (n t k : Nat) (st : Nat × Bool × Bool) : Nat × Bool × Bool :=
  let x := st.1 * st.1 % n
  let live := !st.2.1 && decide (k < t)
  let e1 := decide (x = 1)
  let stop := decide (x = n - 1) || decide (k + 1 = t)
  (if live && !e1 && !stop then x else st.1, st.2.1 || (live && (e1 || stop)), st.2.2 || (live && e1))

/-- The first `k` squarings. -/
def sqIter (n t : Nat) : Nat → Nat × Bool × Bool → Nat × Bool × Bool
  | 0, st => st
  | k + 1, st => sqStep n t k (sqIter n t k st)

/-- The result of a state: `y` if `ok`. -/
def sqRes (st : Nat × Bool × Bool) : Option Nat := if st.2.2 then some st.1 else none

theorem sqStep_done {n t k : Nat} {y : Nat} {ok : Bool} : sqStep n t k (y, true, ok) = (y, true, ok) := by
  simp [sqStep]

theorem sqStep_late {n t k : Nat} (hk : t ≤ k) (st : Nat × Bool × Bool) : sqStep n t k st = st := by
  have : decide (k < t) = false := by simp; omega
  simp [sqStep, this]

/-- A live squaring: done with `squarings 0`'s result if it is the last,
and otherwise with `squarings (j + 1)`'s, or not done and `squarings j`
of the new `y`. -/
theorem sqStep_live {n t k y : Nat} (hk : k < t) :
    let st := sqStep n t k (y, false, false)
    (st.2.1 = true → sqRes st = recoverStep.squarings n (t - 1 - k) y) ∧
    (st.2.1 = false → st.2.2 = false ∧ k + 1 < t ∧
      recoverStep.squarings n (t - 1 - k) y = recoverStep.squarings n (t - 1 - (k + 1)) st.1) := by
  intro st
  have hl : (!false && decide (k < t)) = true := by simp [hk]
  rcases Nat.lt_or_ge (k + 1) t with h1 | h1
  · -- Not the last.
    obtain ⟨j, hj⟩ : ∃ j, t - 1 - k = j + 1 := ⟨t - 1 - k - 1, by omega⟩
    have hj' : t - 1 - (k + 1) = j := by omega
    have hlast : decide (k + 1 = t) = false := by simp; omega
    rw [hj, hj']
    simp only [st, sqStep, hl, hlast, Bool.or_false, recoverStep.squarings, Bool.true_and, Bool.false_or]
    by_cases e1 : y * y % n = 1
    · simp [e1, sqRes]
    · by_cases e2 : y * y % n = n - 1
      · simp [e2, sqRes]
      · simp [e1, e2, h1]
  · -- The last.
    have hj : t - 1 - k = 0 := by omega
    have hlast : decide (k + 1 = t) = true := by simp; omega
    rw [hj]
    simp only [st, sqStep, hl, hlast, Bool.or_true, recoverStep.squarings, Bool.true_and, Bool.false_or]
    by_cases e1 : y * y % n = 1
    · simp [e1, sqRes]
    · simp [e1, sqRes]

/-- What holds after `k ≤ t` squarings, for the overall result `R`. -/
def SqInv (n t : Nat) (R : Option Nat) (k : Nat) (st : Nat × Bool × Bool) : Prop :=
  (st.2.1 = true → sqRes st = R) ∧ (st.2.1 = false → st.2.2 = false ∧ k < t ∧
    R = recoverStep.squarings n (t - 1 - k) st.1)

theorem sqInv_step {n t : Nat} {R : Option Nat} {k : Nat} {st : Nat × Bool × Bool} (h : SqInv n t R k st) :
    SqInv n t R (k + 1) (sqStep n t k st) := by
  rcases st with ⟨y, done, ok⟩
  cases done
  · obtain ⟨hok, hk, hR⟩ := h.2 rfl
    dsimp only at hok
    subst hok
    obtain ⟨a, b⟩ := sqStep_live (n := n) (y := y) hk
    exact ⟨fun hd => (a hd).trans hR.symm, fun hd => by
      obtain ⟨c, d, e⟩ := b hd
      exact ⟨c, d, hR.trans e⟩⟩
  · rw [sqStep_done]
    exact ⟨h.1, fun h' => by simp at h'⟩

/-- `recoverStep`, from `y = g^r mod n`: `done` if `y = ±1`, and otherwise
`squarings (t - 1) y`. -/
theorem recoverStep_eq (n t r g : Nat) :
    recoverStep n t r g = if powMod g r n = 1 ∨ powMod g r n = n - 1 then none
      else recoverStep.squarings n (t - 1) (powMod g r n) := rfl

/-- The start of the squarings. -/
def sqStart (n y : Nat) : Nat × Bool × Bool := (y, decide (y = 1) || decide (y = n - 1), false)

/-- At least `t ≥ 1` squarings: `recoverStep`'s result. -/
theorem sq_result {n t r g K : Nat} (ht : 1 ≤ t) (hK : t ≤ K) :
    sqRes (sqIter n t K (sqStart n (powMod g r n))) = recoverStep n t r g := by
  have h0 : SqInv n t (recoverStep n t r g) 0 (sqStart n (powMod g r n)) := by
    rw [recoverStep_eq]
    by_cases hy : powMod g r n = 1 ∨ powMod g r n = n - 1
    · have hd : (sqStart n (powMod g r n)).2.1 = true := by simpa [sqStart] using hy
      refine ⟨fun _ => ?_, fun h => by rw [hd] at h; cases h⟩
      simp only [hy, ite_true]; rfl
    · have hd : (sqStart n (powMod g r n)).2.1 = false := by simpa [sqStart] using hy
      refine ⟨fun h => (by rw [hd] at h; cases h), fun _ => ⟨rfl, by omega, ?_⟩⟩
      simp only [hy, ite_false, Nat.sub_zero]; rfl
  -- The invariant up to `t`.
  have hI : ∀ k ≤ t, SqInv n t (recoverStep n t r g) k (sqIter n t k (sqStart n (powMod g r n))) := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih => exact sqInv_step (ih (by omega))
  -- Done after `t`.
  have hd : (sqIter n t t (sqStart n (powMod g r n))).2.1 = true := by
    by_contra hnd
    have := (hI t (Nat.le_refl _)).2 (by simpa using hnd)
    omega
  -- Nothing changes after `t`.
  have hlate : ∀ j, sqIter n t (t + j) (sqStart n (powMod g r n)) = sqIter n t t (sqStart n (powMod g r n)) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← Nat.add_assoc, sqIter, ih, sqStep_late (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, K = t + j := ⟨K - t, by omega⟩
  rw [hlate]
  exact (hI t (Nat.le_refl _)).1 hd

/-- The `y` that `squarings` finds has `y² ≡ 1`. -/
theorem squarings_some {n : Nat} : ∀ {j x y : Nat}, recoverStep.squarings n j x = some y → y * y % n = 1
  | 0, x, y, h => by
    simp only [recoverStep.squarings] at h
    split at h
    · cases h; assumption
    · cases h
  | j + 1, x, y, h => by
    simp only [recoverStep.squarings] at h
    split at h
    · cases h; assumption
    · split at h
      · cases h
      · exact squarings_some h

/-- The `y` that `recoverStep` finds has `y² ≡ 1`. -/
theorem recoverStep_some {n t r g y : Nat} (h : recoverStep n t r g = some y) : y * y % n = 1 := by
  rw [recoverStep_eq] at h
  split at h
  · cases h
  · exact squarings_some h

/-! ## The candidates -/

/-- `recoverPrimes.go` from candidate `c` (`g = c + 2`), all those before
having failed. -/
theorem go_eq (n t r : Nat) {c : Nat} (hc : c < recoverTries) :
    recoverPrimes.go n t r (recoverTries - c) =
      match recoverStep n t r (c + 2) with
      | some y => (some (max (Nat.gcd (y - 1) n) (n / Nat.gcd (y - 1) n),
          min (Nat.gcd (y - 1) n) (n / Nat.gcd (y - 1) n)), c + 1)
      | none => recoverPrimes.go n t r (recoverTries - (c + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, recoverTries - c = k + 1 := ⟨recoverTries - c - 1, by omega⟩
  have e1 : recoverTries - k = c + 1 := by omega
  have e2 : recoverTries - (c + 1) = k := by omega
  rw [hk, e2, recoverPrimes.go, e1]
  rfl

theorem go_last (n t r : Nat) : recoverPrimes.go n t r (recoverTries - recoverTries) = (none, recoverTries) := by
  rw [Nat.sub_self, recoverPrimes.go]

/-- `recoverPrimes` when step 1 fails. -/
theorem recoverPrimes_none {n e d : Nat} (h : d * e < 2 ∨ (d * e - 1) % 2 = 1) : recoverPrimes n e d = (none, 0) := by
  simp only [recoverPrimes, h, ite_true]

/-- `recoverPrimes` when step 1 passes: the candidates from `splitTwos (d e - 1)`. -/
theorem recoverPrimes_go {n e d : Nat} (h : ¬(d * e < 2 ∨ (d * e - 1) % 2 = 1)) :
    recoverPrimes n e d =
      recoverPrimes.go n (splitTwos (d * e - 1)).1 (splitTwos (d * e - 1)).2 recoverTries := by
  simp only [recoverPrimes, h, ite_false]

end VG.Proof.Rsa
