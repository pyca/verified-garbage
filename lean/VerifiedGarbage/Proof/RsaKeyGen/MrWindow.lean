module
public import VerifiedGarbage.Proof.RsaKeyGen.Generate
public import VerifiedGarbage.Proof.RsaKeyGen.MillerRabin

import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Bignum.Math

/-!
# Miller–Rabin by windows of 4 bits

For `c − 1 = m 2^a` (`m` odd, `a ≥ 1`), the implementations exponentiate by
`E = (c − 1) / 2^σ` for the shift `σ ∈ [1, 4]` with `σ ≡ a (mod 4)`
(`mrSig`, `mrE`): `E = m 16^v` for `4 v = a − σ`, so a window of 4 bits
ends at `E`'s lowest set bit. A window with digit `d` (`wWin`) squares `y`
four times, or'ing the flag with `y = c − 1` after each, then multiplies `y`
by `b^d mod c`; if `d ≠ 0`, the flag becomes `y = 1 ∨ y = c − 1`. Over the
windows of `E` from its top (`wRun`), `y = b^E mod c` and the flag is
`b^m ≡ ±1` or one of the `4 v` squares of `b^m` after it is `c − 1`
(`FlagOK`): the windows above the lowest nonzero one are forgotten when it
resets the flag. Three more squarings (`wEnd`) or the flag with
`y = c − 1` while fewer than `σ` of them are done: then the squares of
`b^m` up to the `(a − 1)`th have been looked at, which is
`mrIteration`'s result (`wEnd_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Spec.Rsa

/-! ## The shift -/

/-- `a`: the exponent of 2 in `c − 1`. -/
abbrev mrA (c : Nat) : Nat := (splitTwos (c - 1)).1

/-- `σ ∈ [1, 4]` with `σ ≡ a (mod 4)`. -/
def sigOf (a : Nat) : Nat := if a % 4 = 0 then 4 else a % 4

/-- The shift of the exponent. -/
def mrSig (c : Nat) : Nat := sigOf (mrA c)

/-- The exponent: `(c − 1) / 2^σ`. -/
def mrE (c : Nat) : Nat := (c - 1) / 2 ^ mrSig c

theorem sigOf_mod (a : Nat) : sigOf (a % 64) = sigOf a := by
  unfold sigOf; rw [show a % 64 % 4 = a % 4 by omega]

theorem sigOf_pos (a : Nat) : 1 ≤ sigOf a ∧ sigOf a ≤ 4 := by unfold sigOf; split <;> omega

/-- The exponent from `c / 2`, halved under `σ > 1`, `σ > 2` and `σ > 3`. -/
theorem mrE_halves {c : Nat} (hodd : c % 2 = 1) :
    (let e1 := c / 2
     let e2 := if 1 < mrSig c then e1 / 2 else e1
     let e3 := if 2 < mrSig c then e2 / 2 else e2
     if 3 < mrSig c then e3 / 2 else e3) = mrE c := by
  unfold mrE
  have h := sigOf_pos (mrA c)
  have e1 : c / 2 = (c - 1) / 2 ^ 1 := by rw [Nat.pow_one]; omega
  have hd : ∀ k, (c - 1) / 2 ^ k / 2 = (c - 1) / 2 ^ (k + 1) := fun k => by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  simp only
  rw [e1]
  unfold mrSig at *
  rcases (by omega : sigOf (mrA c) = 1 ∨ sigOf (mrA c) = 2 ∨ sigOf (mrA c) = 3 ∨ sigOf (mrA c) = 4)
    with h1 | h1 | h1 | h1 <;> simp [h1, Nat.div_div_eq_div_mul]

/-! ## Squarings -/

theorem sqIter_add (c z s : Nat) : ∀ t, sqIter c z (s + t) = sqIter c (sqIter c z s) t
  | 0 => rfl
  | t + 1 => by rw [← Nat.add_assoc, sqIter, sqIter_add c z s t, sqIter]

/-- `z` squared `t ≥ 1` times is `z^(2^t) mod c`. -/
theorem sqIter_pow (c z : Nat) : ∀ t, 1 ≤ t → sqIter c z t = z ^ (2 ^ t) % c
  | 0, h => absurd h (by decide)
  | 1, _ => by simp only [sqIter, Nat.pow_one, Nat.pow_two]
  | t + 2, _ => by
    rw [sqIter, sqIter_pow c z (t + 1) (by omega), ← Nat.mul_mod, ← Nat.pow_two, ← Nat.pow_mul,
      show 2 ^ (t + 1) * 2 = 2 ^ (t + 2) by rw [← Nat.pow_succ]]

theorem sqIter_lt {c : Nat} (hc : 0 < c) (z : Nat) : ∀ t, 1 ≤ t → sqIter c z t < c
  | 0, h => absurd h (by decide)
  | t + 1, _ => Nat.mod_lt _ hc

theorem sixteen_pow (t : Nat) : (16 : Nat) ^ t = 2 ^ (4 * t) := by rw [Nat.pow_mul]

/-- A squaring: `y := y²`, the flag or'ed with `y = c − 1` if `m`. -/
def wSq (c : Nat) (m : Bool) (st : Nat × Bool) : Nat × Bool :=
  (st.1 * st.1 % c, st.2 || (m && decide (st.1 * st.1 % c = c - 1)))

/-- `n` squarings, each or'ing the flag. -/
def sqs (c : Nat) : Nat → Nat × Bool → Nat × Bool
  | 0, st => st
  | n + 1, st => wSq c true (sqs c n st)

theorem sqs_fst (c : Nat) (st : Nat × Bool) : ∀ n, (sqs c n st).1 = sqIter c st.1 n
  | 0 => rfl
  | n + 1 => by simp only [sqs, wSq, sqs_fst c st n, sqIter]

theorem sqs_snd (c : Nat) (st : Nat × Bool) : ∀ n, ((sqs c n st).2 = true ↔
    (st.2 = true ∨ ∃ i, 1 ≤ i ∧ i ≤ n ∧ sqIter c st.1 i = c - 1))
  | 0 => by
    simp only [sqs]
    exact ⟨Or.inl, fun h => h.elim id fun ⟨i, h1, h2, _⟩ => absurd h2 (by omega)⟩
  | n + 1 => by
    simp only [sqs, wSq, Bool.or_eq_true, Bool.true_and, decide_eq_true_eq]
    rw [sqs_snd c st n, sqs_fst c st n]
    constructor
    · rintro ((h | ⟨i, h1, h2, h3⟩) | h)
      · exact .inl h
      · exact .inr ⟨i, h1, by omega, h3⟩
      · exact .inr ⟨n + 1, by omega, Nat.le_refl _, by rw [sqIter]; exact h⟩
    · rintro (h | ⟨i, h1, h2, h3⟩)
      · exact .inl (.inl h)
      · rcases Nat.lt_or_ge i (n + 1) with hi | hi
        · exact .inl (.inr ⟨i, h1, by omega, h3⟩)
        · rw [show i = n + 1 by omega, sqIter] at h3; exact .inr h3

/-! ## Windows -/

/-- A window with digit `d`: four squarings, then `y b^d`, and the flag
reset to `y = ±1` if `d ≠ 0`. -/
def wWin (c b d : Nat) (st : Nat × Bool) : Nat × Bool :=
  let s := wSq c true (wSq c true (wSq c true (wSq c true st)))
  (s.1 * powMod b d c % c,
    if d = 0 then s.2 else decide (s.1 * powMod b d c % c = 1) || decide (s.1 * powMod b d c % c = c - 1))

/-- The top `j` of the `W` windows of `E`, from `y = 1` and a clear flag. -/
def wRun (c b E W : Nat) : Nat → Nat × Bool
  | 0 => (1, false)
  | j + 1 => wWin c b (E / 16 ^ (W - 1 - j) % 16) (wRun c b E W j)

/-- The three squarings after the windows. -/
def wEnd (c : Nat) (st : Nat × Bool) : Nat × Bool :=
  wSq c (decide (3 < mrSig c)) (wSq c (decide (2 < mrSig c)) (wSq c (decide (1 < mrSig c)) st))

/-- The flag after the windows of `X`: clear for `X = 0`; for
`X = Y 16^t` with `Y`'s low digit nonzero, `b^Y ≡ ±1` or one of the `4 t`
squares after it is `c − 1`. -/
def FlagOK (c b X : Nat) (P : Bool) : Prop :=
  (X = 0 → P = false) ∧ ∀ Y t, X = Y * 16 ^ t → Y % 16 ≠ 0 →
    (P = true ↔ (powMod b Y c = 1 ∨ powMod b Y c = c - 1 ∨
      ∃ i, 1 ≤ i ∧ i ≤ 4 * t ∧ sqIter c (powMod b Y c) i = c - 1))

theorem powMod_zero' {b c : Nat} (hc : 1 < c) : powMod b 0 c = 1 := by
  rw [VG.Proof.Bignum.powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt hc]

/-- A window's power: `b^(16 X + d) = (b^X)^16 b^d`. -/
theorem powMod_win (b X d c : Nat) :
    powMod b (16 * X + d) c = sqIter c (powMod b X c) 4 * powMod b d c % c := by
  rw [sqIter_pow c _ 4 (by decide), VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq,
    VG.Proof.Bignum.powMod_eq, ← Nat.pow_mod, ← Nat.mul_mod, ← Nat.pow_mul, ← Nat.pow_add,
    show 16 * X = X * 2 ^ 4 by omega]

/-- One window. -/
theorem win_step {c b X d : Nat} {P : Bool} (hc : 3 ≤ c) (hd : d < 16) (hF : FlagOK c b X P) :
    (wWin c b d (powMod b X c, P)).1 = powMod b (16 * X + d) c ∧
    FlagOK c b (16 * X + d) (wWin c b d (powMod b X c, P)).2 := by
  have h4 : wSq c true (wSq c true (wSq c true (wSq c true (powMod b X c, P)))) =
      sqs c 4 (powMod b X c, P) := rfl
  have hy : (wWin c b d (powMod b X c, P)).1 = powMod b (16 * X + d) c := by
    simp only [wWin, h4, sqs_fst]; exact (powMod_win b X d c).symm
  refine ⟨hy, ?_⟩
  by_cases hd0 : d = 0
  · subst hd0
    have hP : (wWin c b 0 (powMod b X c, P)).2 = (sqs c 4 (powMod b X c, P)).2 := by
      simp only [wWin, h4, ↓reduceIte]
    rw [hP, Nat.add_zero]
    by_cases hX : X = 0
    · subst hX
      have hP0 := hF.1 rfl
      have hy1 : powMod b 0 c = 1 := powMod_zero' (by omega)
      refine ⟨fun _ => ?_, fun Y t hYt hY => absurd (by
        rcases Nat.eq_zero_or_pos Y with h | h
        · subst h; rfl
        · exact absurd hYt.symm (Nat.ne_of_gt (Nat.mul_pos h (Nat.pow_pos (by decide))))) hY⟩
      apply Bool.eq_false_iff.mpr
      intro h
      rw [sqs_snd] at h
      rcases h with h | ⟨i, _, _, hi⟩
      · rw [hP0] at h; cases h
      · simp only [hy1, sqIter_one c (by omega)] at hi; omega
    · refine ⟨fun h => absurd h (by omega), fun Y t hYt hY => ?_⟩
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := by
        rcases t with _ | t
        · rw [Nat.pow_zero, Nat.mul_one] at hYt; omega
        · exact ⟨t, rfl⟩
      have hXY : X = Y * 16 ^ t := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (Y * 16 ^ t) 16] at hYt
        exact Nat.eq_of_mul_eq_mul_left (by decide) hYt
      have hYp : 0 < Y := by omega
      have hz : powMod b X c = sqIter c (powMod b Y c) (4 * t) := by
        rw [hXY, sixteen_pow]
        exact powMod_pow2 b Y c hYp (4 * t)
      rw [sqs_snd, hF.2 Y t hXY hY]
      simp only [hz, ← sqIter_add]
      constructor
      · rintro ((h | h | ⟨i, h1, h2, h3⟩) | ⟨i, h1, h2, h3⟩)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr ⟨i, h1, by omega, h3⟩)
        · exact .inr (.inr ⟨4 * t + i, by omega, by omega, h3⟩)
      · rintro (h | h | ⟨i, h1, h2, h3⟩)
        · exact .inl (.inl h)
        · exact .inl (.inr (.inl h))
        · rcases Nat.lt_or_ge (4 * t) i with hi | hi
          · exact .inr ⟨i - 4 * t, by omega, by omega, by rw [Nat.add_sub_cancel' (Nat.le_of_lt hi)]; exact h3⟩
          · exact .inl (.inr (.inr ⟨i, h1, hi, h3⟩))
  · have hP : (wWin c b d (powMod b X c, P)).2 =
        (decide (powMod b (16 * X + d) c = 1) || decide (powMod b (16 * X + d) c = c - 1)) := by
      rw [← hy]; simp only [wWin, hd0, ↓reduceIte]
    rw [hP]
    refine ⟨fun h => absurd h (by omega), fun Y t hYt hY => ?_⟩
    have ht : t = 0 := by
      rcases t with _ | t
      · rfl
      · exfalso
        have : (16 * X + d) % 16 = 0 := by rw [hYt, Nat.pow_succ, ← Nat.mul_assoc]; exact Nat.mul_mod_left _ _
        omega
    subst ht
    rw [Nat.pow_zero, Nat.mul_one] at hYt
    subst hYt
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact .inr (.inl h)
    · rintro (h | h | ⟨i, h1, h2, _⟩)
      · exact .inl h
      · exact .inr h
      · omega

/-- The windows so far: `y = b^X mod c` and the flag of `X`, for the top
`X` of `E`. -/
theorem wRun_ok {c b E W : Nat} (hc : 3 ≤ c) (hE : E < 16 ^ W) : ∀ j, j ≤ W →
    (wRun c b E W j).1 = powMod b (E / 16 ^ (W - j)) c ∧ FlagOK c b (E / 16 ^ (W - j)) (wRun c b E W j).2
  | 0, _ => by
    rw [Nat.sub_zero, Nat.div_eq_of_lt hE]
    exact ⟨(powMod_zero' (by omega)).symm, fun _ => rfl, fun Y t hYt hY => absurd (by
      rcases Nat.eq_zero_or_pos Y with h | h
      · subst h; rfl
      · exact absurd hYt.symm (Nat.ne_of_gt (Nat.mul_pos h (Nat.pow_pos (by decide))))) hY⟩
  | j + 1, hj => by
    obtain ⟨hy, hF⟩ := wRun_ok hc hE j (by omega)
    have e : E / 16 ^ (W - (j + 1)) = 16 * (E / 16 ^ (W - j)) + E / 16 ^ (W - 1 - j) % 16 := by
      rw [show W - j = (W - 1 - j) + 1 by omega, show W - (j + 1) = W - 1 - j by omega, Nat.pow_succ,
        ← Nat.div_div_eq_div_mul]
      omega
    rw [wRun, show wRun c b E W j = (powMod b (E / 16 ^ (W - j)) c, (wRun c b E W j).2) by rw [← hy],
      e]
    exact win_step hc (Nat.mod_lt _ (by decide)) hF

theorem sigOf_le {a : Nat} (ha : 1 ≤ a) : sigOf a ≤ a := by unfold sigOf; split <;> omega

theorem sigOf_sub {a : Nat} : (a - sigOf a) % 4 = 0 := by unfold sigOf; split <;> omega

theorem sigOf_lt {a : Nat} (ha : 1 ≤ a) : a - sigOf a + sigOf a = a := by have := sigOf_le ha; omega

theorem wSq_iter (c z n : Nat) (m P : Bool) :
    wSq c m (sqIter c z n, P) = (sqIter c z (n + 1), P || (m && decide (sqIter c z (n + 1) = c - 1))) := rfl

/-- The flag of `E = m 16^v` and the three squarings, `σ` of them counted:
`b^m ≡ 1`, or `b^m` squared fewer than `4 v + σ` times is `c − 1`. -/
theorem wEnd_flag {c b m v σ y : Nat} {P : Bool} (hσ1 : 1 ≤ σ) (hσ : σ ≤ 4)
    (hP : P = true ↔ (powMod b m c = 1 ∨ powMod b m c = c - 1 ∨
      ∃ i, 1 ≤ i ∧ i ≤ 4 * v ∧ sqIter c (powMod b m c) i = c - 1))
    (hy : y = sqIter c (powMod b m c) (4 * v)) :
    ((wSq c (decide (3 < σ)) (wSq c (decide (2 < σ)) (wSq c (decide (1 < σ)) (y, P)))).2 = true ↔
      (powMod b m c = 1 ∨ ∃ t, t < 4 * v + σ ∧ sqIter c (powMod b m c) t = c - 1)) := by
  generalize powMod b m c = z at hP hy
  subst hy
  rw [wSq_iter, wSq_iter, wSq_iter]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [hP]
  constructor
  · rintro ((((h | h | ⟨i, h1, h2, h3⟩) | ⟨h4, h5⟩) | ⟨h4, h5⟩) | ⟨h4, h5⟩)
    · exact .inl h
    · exact .inr ⟨0, by omega, h⟩
    · exact .inr ⟨i, by omega, h3⟩
    · exact .inr ⟨4 * v + 1, by omega, h5⟩
    · exact .inr ⟨4 * v + 1 + 1, by omega, h5⟩
    · exact .inr ⟨4 * v + 1 + 1 + 1, by omega, h5⟩
  · rintro (h | ⟨t, ht, h3⟩)
    · exact .inl (.inl (.inl (.inl h)))
    · rcases t with _ | t
      · exact .inl (.inl (.inl (.inr (.inl h3))))
      · rcases Nat.lt_or_ge (t + 1) (4 * v + 1) with h | h
        · exact .inl (.inl (.inl (.inr (.inr ⟨t + 1, by omega, by omega, h3⟩))))
        · have e : t + 1 = 4 * v + 1 ∨ t + 1 = 4 * v + 1 + 1 ∨ t + 1 = 4 * v + 1 + 1 + 1 := by omega
          rcases e with e | e | e <;> rw [e] at h3
          · exact .inl (.inl (.inr ⟨by omega, h3⟩))
          · exact .inl (.inr ⟨by omega, h3⟩)
          · exact .inr ⟨by omega, h3⟩

/-- The windows of `E` and the three squarings: `mrIteration`'s result. -/
theorem wEnd_eq {c W : Nat} (b : Nat) (hc : 3 ≤ c) (hodd : c % 2 = 1) (haw : mrA c ≤ bitLength c - 1)
    (hE : mrE c < 16 ^ W) :
    (wEnd c (wRun c b (mrE c) W W)).2 = mrIteration c (mrA c) (splitTwos (c - 1)).2 b := by
  obtain ⟨hN, hm2⟩ := splitTwos_spec (c - 1) (by omega)
  have hm16 : (splitTwos (c - 1)).2 % 16 ≠ 0 := by omega
  change c - 1 = (splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  have hEd : mrE c = (c - 1) / 2 ^ sigOf (mrA c) := rfl
  have hsd : mrSig c = sigOf (mrA c) := rfl
  obtain ⟨hy, hF⟩ := wRun_ok (b := b) hc hE W (Nat.le_refl _)
  rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hy hF
  unfold wEnd
  generalize wRun c b (mrE c) W W = st at hy hF
  obtain ⟨y, P⟩ := st
  simp only at hy hF ⊢
  rw [hsd]
  generalize hE' : mrE c = E at hy hF hEd
  generalize hm : (splitTwos (c - 1)).2 = m at hN hm2 hm16 ⊢
  generalize ha : mrA c = a at hN haw hEd ⊢
  subst hEd
  have hmp : 0 < m := by omega
  have ha1 : 1 ≤ a := by
    rcases a with _ | a
    · rw [Nat.pow_zero, Nat.mul_one] at hN; omega
    · omega
  have hsig := sigOf_pos a
  have hσa := sigOf_le ha1
  obtain ⟨v, hv'⟩ : ∃ v, a - sigOf a = 4 * v := ⟨(a - sigOf a) / 4, by have := sigOf_sub (a := a); omega⟩
  have has : 4 * v + sigOf a = a := by rw [← hv']; exact Nat.sub_add_cancel hσa
  have hEm : (c - 1) / 2 ^ sigOf a = m * 16 ^ v := by
    have h2 : 2 ^ a = 2 ^ (a - sigOf a) * 2 ^ sigOf a := by rw [← Nat.pow_add, Nat.sub_add_cancel hσa]
    rw [hN, h2, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _), hv', sixteen_pow]
  rw [hEm] at hy hF
  have hflag := hF.2 m v rfl hm16
  have hyz : y = sqIter c (powMod b m c) (4 * v) := by
    rw [hy, sixteen_pow]
    exact powMod_pow2 b m c hmp (4 * v)
  apply Bool.eq_iff_iff.mpr
  rw [wEnd_flag hsig.1 hsig.2 hflag hyz, mrIteration_iff hc ha1 haw, has]

/-- For a candidate of `64 w` bits: the windows of its `16 w` digits. -/
theorem wEnd_cand {w c : Nat} (b : Nat) (hw : 1 ≤ w) (hc : PrimeShape (64 * w) c) :
    (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 =
      mrIteration c (splitTwos (c - 1)).1 (splitTwos (c - 1)).2 b := by
  obtain ⟨hb, _, _⟩ := cand_bits hw hc
  obtain ⟨hodd, hlo, hhi⟩ := hc
  have : 4 ≤ 2 ^ (64 * w - 2) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨hN, _⟩ := splitTwos_spec (c - 1) (by omega)
  change c - 1 = (splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  have haT : mrA c < 64 * w := by
    rcases Nat.lt_or_ge (mrA c) (64 * w) with h | h
    · exact h
    exfalso
    have : 2 ^ (64 * w) ≤ 2 ^ mrA c := Nat.pow_le_pow_right (by decide) h
    have : 2 ^ mrA c ≤ (splitTwos (c - 1)).2 * 2 ^ mrA c :=
      Nat.le_mul_of_pos_left _ (by rcases Nat.eq_zero_or_pos (splitTwos (c - 1)).2 with h0 | h0
                                   · rw [h0, Nat.zero_mul] at hN; omega
                                   · exact h0)
    omega
  refine wEnd_eq b (by omega) hodd (by rw [hb]; omega) ?_
  have : mrE c ≤ c - 1 := Nat.div_le_self _ _
  rw [sixteen_pow, show 4 * (16 * w) = 64 * w by omega]
  omega

/-! ## The lowest set bit -/

/-- `x & −x` is `x`'s lowest set bit. -/
theorem and_neg_eq_twoPow {x : BitVec 64} {k : Nat} (hk : k < 64) (h1 : x.getLsbD k = true)
    (h0 : ∀ j < k, x.getLsbD j = false) : x &&& -x = BitVec.twoPow 64 k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_neg, BitVec.getLsbD_twoPow]
  rcases Nat.lt_trichotomy i k with h | rfl | h
  · rw [h0 i h, decide_eq_false (show ¬ k = i by omega)]; simp
  · rw [h1]
    have : ¬ ∃ j < i, x.getLsbD j = true := fun ⟨j, hj, hj'⟩ => by rw [h0 j hj] at hj'; cases hj'
    simp [this, hk]
  · have : ∃ j < i, x.getLsbD j = true := ⟨k, h, h1⟩
    rw [decide_eq_false (show ¬ k = i by omega)]
    cases x.getLsbD i <;> simp [this, hi]

/-- The words of `N = m 2^a` (`m` odd) below the one with bit `a` are zero,
and that one has its lowest set bit at `a mod 64`. -/
theorem lowWord_bits {N m a : Nat} (hN : N = m * 2 ^ a) (hm : m % 2 = 1) :
    (∀ j < a / 64, N / 2 ^ (64 * j) % 2 ^ 64 = 0) ∧
    (N / 2 ^ (64 * (a / 64)) % 2 ^ 64).testBit (a % 64) = true ∧
    ∀ j < a % 64, (N / 2 ^ (64 * (a / 64)) % 2 ^ 64).testBit j = false := by
  have hb : ∀ i, N.testBit i = (decide (a ≤ i) && m.testBit (i - a)) := fun i => by
    rw [hN, Nat.testBit_mul_two_pow]
  refine ⟨fun j hj => Nat.eq_of_testBit_eq fun i => ?_, ?_, fun j hj => ?_⟩
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hb, Nat.zero_testBit]
    by_cases hi : i < 64
    · simp only [hi, decide_true, Bool.true_and]; simp only [Bool.and_eq_false_iff]; left; simp; omega
    · simp [hi]
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hb]
    simp only [show a % 64 < 64 by omega, decide_true, Bool.true_and, show a ≤ a % 64 + 64 * (a / 64) by omega,
      show a % 64 + 64 * (a / 64) - a = 0 by omega]
    rw [Nat.testBit_zero]; simp [hm]
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hb]
    simp only [show j < 64 by omega, decide_true, Bool.true_and, Bool.and_eq_false_iff]
    left; simp; omega

/-- The masks of `σ > 1`, `σ > 2` and `σ > 3` from the lowest set bit
`2^k`: `l & K ≠ 0` for the constants of the implementations. -/
theorem sig_mask1 : ∀ k < 64, (BitVec.twoPow 64 k &&& 0xDDDDDDDDDDDDDDDD#64 = 0) = ¬ (1 < sigOf k) := by
  decide

theorem sig_mask2 : ∀ k < 64, (BitVec.twoPow 64 k &&& 0x9999999999999999#64 = 0) = ¬ (2 < sigOf k) := by
  decide

theorem sig_mask3 : ∀ k < 64, (BitVec.twoPow 64 k &&& 0x1111111111111111#64 = 0) = ¬ (3 < sigOf k) := by
  decide

/-! ## The windows of a word -/

/-- The digit at the top of a word shifted left by `4 t`: digit `15 − t`. -/
theorem shl_shr60 (x : BitVec 64) {t : Nat} (ht : t < 16) :
    ((x <<< (4 * t)) >>> 60).toNat = x.toNat / 2 ^ (60 - 4 * t) % 2 ^ 4 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hi : i < 4
  · simp only [show i + 60 < 64 by omega, hi, decide_true, Bool.true_and, show 4 * t ≤ i + 60 by omega]
    congr 1; omega
  · simp only [show ¬ i + 60 < 64 by omega, hi, decide_false, Bool.false_and]

theorem mod_div_mod {x a b n : Nat} (h : a + b ≤ n) : x % 2 ^ n / 2 ^ a % 2 ^ b = x / 2 ^ a % 2 ^ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hi : i < b
  · simp [hi, show i + a < n by omega]
  · simp [hi]

/-- The digit of the window: digit `16 (k − 1) + 15 − t` of `E`. -/
theorem win_digit {W : BitVec 64} {E k t : Nat} (hW : W.toNat = E / 2 ^ (64 * (k - 1)) % 2 ^ 64) (ht : t < 16) :
    ((W <<< (4 * t)) >>> 60).toNat = E / 16 ^ (16 * (k - 1) + (15 - t)) % 16 := by
  rw [shl_shr60 W ht, hW, mod_div_mod (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add, sixteen_pow,
    show 64 * (k - 1) + (60 - 4 * t) = 4 * (16 * (k - 1) + (15 - t)) by omega]

theorem shl4_succ (x : BitVec 64) (t : Nat) : x <<< (4 * t) <<< 4 = x <<< (4 * (t + 1)) := by
  rw [← BitVec.shiftLeft_add, show 4 * t + 4 = 4 * (t + 1) by omega]

end VG.Proof.RsaKeyGen
