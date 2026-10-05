import VerifiedGarbage.Spec.RsaKeyGen

/-!
# Miller–Rabin without splitting `w − 1`

`mrIteration w a m b` (`Spec/RsaKeyGen.lean`) squares `z = b^m mod w`, for
`w − 1 = 2^a m`, up to `a` times. The implementations compute instead the
powers `y_i = b^⌊(w − 1) / 2^i⌋ mod w` from the top bit of `w − 1` down
(square, then multiply by `b` if bit `i` is set), and keep a flag `P`:
at a set bit `i` it becomes `y_i = 1 ∨ y_i = w − 1`, at a clear one it is
or'ed with `y_i = w − 1` (`mrRun`). The lowest set bit is `a`, and below it
`y_i` is `z` squared `a − i` times, so after bit 1 the flag is
`mrIteration`'s result (`mrRun_eq`), without `a` or `m`: the code needs no
shift by a secret amount.
-/

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Spec.Rsa

/-! ## `mrSquarings` -/

/-- With `possible` set, the squarings end with it. -/
theorem mrSquarings_true (w a : Nat) : ∀ fuel j z, mrSquarings w a fuel j z true = true
  | 0, _, _ => rfl
  | fuel + 1, j, z => by
    simp only [mrSquarings, Bool.not_true, Bool.false_eq_true, and_false, ↓reduceIte, Bool.true_or,
      Bool.and_false]
    exact mrSquarings_true w a fuel (j + 1) _

/-- `z` squared `t` times modulo `w`. -/
def sqIter (w z : Nat) : Nat → Nat
  | 0 => z
  | t + 1 => sqIter w z t * sqIter w z t % w

theorem sqIter_succ' (w z t : Nat) : sqIter w z (t + 1) = sqIter w (z * z % w) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [sqIter, ih, sqIter]

theorem sqIter_one (w : Nat) (hw : 2 ≤ w) : ∀ t, sqIter w 1 t = 1
  | 0 => rfl
  | t + 1 => by rw [sqIter, sqIter_one w hw t, Nat.one_mul, Nat.mod_eq_of_lt (by omega)]

/-- The squarings from `j ≤ a`, with `z` the value after `j − 1` of them:
`possible`, or one of the next `a − j` squares is `w − 1`. -/
theorem mrSquarings_iff (w a : Nat) (hw : 3 ≤ w) :
    ∀ fuel j z possible, 1 ≤ j → j ≤ a → a ≤ fuel + j - 1 →
      (mrSquarings w a fuel j z possible = true ↔
        (possible = true ∨ ∃ t, 1 ≤ t ∧ t ≤ a - j ∧ sqIter w z t = w - 1))
  | 0, j, _, _, h1, hja, haf => by omega
  | fuel + 1, j, z, possible, h1, hja, haf => by
    rcases Nat.lt_or_ge j a with hlt | hge
    · have hne : ¬ (j = a ∧ (!possible) = true) := fun h => by omega
      simp only [mrSquarings, hne, ↓reduceIte]
      by_cases hz : (z * z % w == 1 && !(possible || z * z % w == w - 1)) = true
      · simp only [hz, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
          beq_eq_false_iff_ne] at hz
        obtain ⟨hz1, hp, -⟩ := hz
        simp only [hp, Bool.false_or, beq_iff_eq, Bool.false_eq_true, false_or]
        constructor
        · intro h; omega
        · rintro ⟨t, ht, _, he⟩
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          rw [sqIter_succ', hz1, sqIter_one w (by omega)] at he
          omega
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        rw [mrSquarings_iff w a hw fuel (j + 1) _ _ (by omega) (by omega) (by omega)]
        simp only [Bool.or_eq_true, beq_iff_eq]
        constructor
        · rintro ((hp | he) | ⟨t, ht1, ht2, he⟩)
          · exact .inl hp
          · exact .inr ⟨1, Nat.le_refl _, by omega, by rw [sqIter, sqIter]; exact he⟩
          · exact .inr ⟨t + 1, by omega, by omega, by rw [sqIter_succ']; exact he⟩
        · rintro (hp | ⟨t, ht1, ht2, he⟩)
          · exact .inl (.inl hp)
          · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
            rcases t' with _ | t'
            · exact .inl (.inr (by rw [sqIter, sqIter] at he; exact he))
            · exact .inr ⟨t' + 1, by omega, by omega, by rw [← sqIter_succ']; exact he⟩
    · have hj : j = a := by omega
      subst hj
      cases possible
      · simp only [mrSquarings, Bool.not_false, and_self, ↓reduceIte, Bool.false_eq_true, false_or]
        constructor
        · intro h; exact absurd h (by decide)
        · rintro ⟨t, h1, h2, _⟩; omega
      · simp [mrSquarings_true]

/-- `mrIteration`: `z = b^m mod w` is 1, or it squared fewer than `a` times
is `w − 1`. -/
theorem mrIteration_iff {w a m b : Nat} (hw : 3 ≤ w) (ha : 1 ≤ a) (haw : a ≤ bitLength w - 1) :
    mrIteration w a m b = true ↔ (powMod b m w = 1 ∨
      ∃ t, t < a ∧ sqIter w (powMod b m w) t = w - 1) := by
  unfold mrIteration
  simp only
  rw [mrSquarings_iff w a hw _ 1 _ _ (Nat.le_refl _) ha (by omega)]
  simp only [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ((h | h) | ⟨t, _, ht, he⟩)
    · exact .inl h
    · exact .inr ⟨0, ha, h⟩
    · exact .inr ⟨t, by omega, he⟩
  · rintro (h | ⟨t, ht, he⟩)
    · exact .inl (.inl h)
    · rcases t with _ | t
      · exact .inl (.inr he)
      · exact .inr ⟨t + 1, by omega, by omega, he⟩

/-! ## Powers from the top bit -/

/-- `powMod` of an even exponent `2 e > 0`. -/
theorem powMod_double (b e w : Nat) (he : 0 < e) :
    powMod b (2 * e) w = powMod b e w * powMod b e w % w := by
  rw [powMod]
  simp only [show 2 * e ≠ 0 by omega, ↓reduceIte, show 2 * e / 2 = e by omega,
    show 2 * e % 2 = 0 by omega]

/-- `b^(m 2^t)` is `b^m` squared `t` times. -/
theorem powMod_pow2 (b m w : Nat) (hm : 0 < m) :
    ∀ t, powMod b (m * 2 ^ t) w = sqIter w (powMod b m w) t
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]; rfl
  | t + 1 => by
    rw [sqIter, ← powMod_pow2 b m w hm t, show m * 2 ^ (t + 1) = 2 * (m * 2 ^ t) by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm]]
    exact powMod_double b _ w (Nat.mul_pos hm (Nat.two_pow_pos _))

/-- One step of the flag at bit `i` of `N = w − 1`: `y_i` is
`b^⌊N / 2^i⌋ mod w`. -/
def mrFlag (w b i : Nat) (P : Bool) : Bool :=
  let y := powMod b ((w - 1) / 2 ^ i) w
  if (w - 1) / 2 ^ i % 2 = 1 then (y == 1 || y == w - 1) else (P || y == w - 1)

/-- The flag over bits `k, k − 1, …, 1`. -/
def mrRun (w b : Nat) : Nat → Bool → Bool
  | 0, P => P
  | k + 1, P => mrRun w b k (mrFlag w b (k + 1) P)

theorem splitTwos_spec : ∀ n, 0 < n → n = (splitTwos n).2 * 2 ^ (splitTwos n).1 ∧ (splitTwos n).2 % 2 = 1
  | n, hn => by
    rw [splitTwos]
    by_cases h : n = 0 ∨ n % 2 = 1
    · simp only [h, ↓reduceIte, Nat.pow_zero, Nat.mul_one, true_and]; omega
    · simp only [h, ↓reduceIte]
      obtain ⟨h1, h2⟩ := splitTwos_spec (n / 2) (by omega)
      refine ⟨?_, h2⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← h1]; omega
termination_by n => n
decreasing_by omega

/-- Below the lowest set bit `a` of `N = m 2^a`: the flag or'ed with the
squares. -/
theorem mrRun_low (w b m a : Nat) (hm : 0 < m) (hN : w - 1 = m * 2 ^ a) :
    ∀ k, k < a → ∀ P, (mrRun w b k P = true ↔
      (P = true ∨ ∃ i, 1 ≤ i ∧ i ≤ k ∧ sqIter w (powMod b m w) (a - i) = w - 1))
  | 0, _, P => by simp only [mrRun]; constructor; exact .inl; rintro (h | ⟨i, h1, h2, _⟩); exact h; omega
  | k + 1, hk, P => by
    rw [mrRun, mrRun_low w b m a hm hN k (by omega)]
    have hdiv : (w - 1) / 2 ^ (k + 1) = m * 2 ^ (a - (k + 1)) := by
      rw [hN, show a = (a - (k + 1)) + (k + 1) by omega, Nat.pow_add, ← Nat.mul_assoc,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.add_sub_cancel]
    have hpar : (w - 1) / 2 ^ (k + 1) % 2 = 0 := by
      rw [hdiv, show a - (k + 1) = (a - (k + 1) - 1) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_mod_left _ _
    unfold mrFlag
    rw [hdiv] at hpar
    simp only [hdiv, powMod_pow2 b m w hm, hpar, Nat.zero_ne_one, ↓reduceIte, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ((hp | he) | ⟨i, h1, h2, he⟩)
      · exact .inl hp
      · exact .inr ⟨k + 1, by omega, Nat.le_refl _, he⟩
      · exact .inr ⟨i, h1, by omega, he⟩
    · rintro (hp | ⟨i, h1, h2, he⟩)
      · exact .inl (.inl hp)
      · rcases Nat.lt_or_ge i (k + 1) with h | h
        · exact .inr ⟨i, h1, by omega, he⟩
        · exact .inl (.inr (by rw [show i = k + 1 by omega] at he; exact he))

/-- At and above the lowest set bit, the flag only matters from it on. -/
theorem mrRun_high (w b m a : Nat) (hm : 0 < m) (hm2 : m % 2 = 1) (hN : w - 1 = m * 2 ^ a)
    (ha : 1 ≤ a) : ∀ k, a ≤ k → ∀ P, mrRun w b k P = mrRun w b (a - 1) (mrFlag w b a false)
  | 0, hk, _ => by omega
  | k + 1, hk, P => by
    rcases Nat.lt_or_ge a (k + 1) with h | h
    · rw [mrRun, mrRun_high w b m a hm hm2 hN ha k (by omega)]
    · have hka : k + 1 = a := by omega
      subst hka
      rw [mrRun, Nat.add_sub_cancel]
      congr 1
      have hdiv : (w - 1) / 2 ^ (k + 1) = m := by
        rw [hN, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      unfold mrFlag
      simp only [hdiv, hm2, ↓reduceIte]

/-- The flag over the bits `T − 1, …, 1` of `w − 1`, for `w − 1 < 2^T`, is
`mrIteration`'s result, whatever it starts as. -/
theorem mrRun_eq {w b T : Nat} (hw : 3 ≤ w) (hw2 : w % 2 = 1) (hT : w - 1 < 2 ^ T)
    (hTw : T - 1 ≤ bitLength w - 1) (P : Bool) :
    mrRun w b (T - 1) P =
      mrIteration w (splitTwos (w - 1)).1 (splitTwos (w - 1)).2 b := by
  apply Bool.eq_iff_iff.mpr
  obtain ⟨hN, hm2⟩ := splitTwos_spec (w - 1) (by omega)
  generalize (splitTwos (w - 1)).1 = a at hN hm2 ⊢
  generalize (splitTwos (w - 1)).2 = m at hN hm2 ⊢
  have hm : 0 < m := by omega
  have ha : 1 ≤ a := by
    rcases a with _ | a
    · rw [Nat.pow_zero, Nat.mul_one] at hN; omega
    · omega
  have haT : a < T := by
    rcases Nat.lt_or_ge a T with h | h
    · exact h
    exfalso
    have : 2 ^ T ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ a ≤ m * 2 ^ a := Nat.le_mul_of_pos_left _ hm
    omega
  rw [mrRun_high w b m a hm hm2 hN ha (T - 1) (by omega) P, mrRun_low w b m a hm hN (a - 1) (by omega),
    mrIteration_iff hw ha (by omega)]
  have hdiv : (w - 1) / 2 ^ a = m := by rw [hN, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  unfold mrFlag
  simp only [hdiv, hm2, ↓reduceIte]
  simp only [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ((h | h) | ⟨i, h1, h2, he⟩)
    · exact .inl h
    · exact .inr ⟨0, by omega, h⟩
    · exact .inr ⟨a - i, by omega, he⟩
  · rintro (h | ⟨t, ht, he⟩)
    · exact .inl (.inl h)
    · rcases t with _ | t
      · exact .inl (.inr he)
      · exact .inr ⟨a - (t + 1), by omega, by omega, by rw [show a - (a - (t + 1)) = t + 1 by omega]; exact he⟩

end VG.Proof.RsaKeyGen
