module

public import VerifiedGarbage.Spec.RsaKeyGen

/-!
# Miller–Rabin without splitting `w − 1`

`mrIteration w a m b` (`Spec/RsaKeyGen.lean`) squares `z = b^m mod w`, for
`w − 1 = 2^a m`, up to `a` times. The implementations compute instead the
powers `y_i = b^⌊(w − 1) / 2^i⌋ mod w` from the top bit of `w − 1` down
(square, then multiply by `b` if bit `i` is set), and keep a flag `P`:
at a set bit `i` it becomes `y_i = 1 ∨ y_i = w − 1`, at a clear one it is
or'ed with `y_i = w − 1`. The lowest set bit is `a`, and below it
`y_i` is `z` squared `a − i` times (`powMod_pow2`), so after bit 1 the flag
is `mrIteration`'s result, without `a` or `m`: the code needs no shift by a
secret amount.
-/

@[expose] public section

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

end VG.Proof.RsaKeyGen
