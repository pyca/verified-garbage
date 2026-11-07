module

public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the arithmetic alone, which the IFMA round's proofs share without its code's

/-!
# Miller–Rabin by windows of `k` bits

`Proof/RsaKeyGen/MrWindow.lean`'s windows of 4 bits, for any width `k ≥ 1`
dividing 4: `E = mrE c = m 16^v = m (2^k)^(4 v / k)` still has its lowest set
bit at the end of a window, so the flag after the windows of `E` (`kRun`) and
`MrWindow`'s three squarings (`wEnd`) is `mrIteration`'s result (`kEnd_eq`).
A window with digit `d < 2^k` (`kWin`) squares `y` `k` times, or'ing the flag
with `y = c − 1` after each, then multiplies `y` by `b^d mod c`; if `d ≠ 0`
the flag becomes `y = 1 ∨ y = c − 1`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.WindowK

open VG.Spec.RsaKeyGen VG.Spec.Rsa VG.Proof.RsaKeyGen

/-- A window of `k` bits with digit `d`. -/
def kWin (k c b d : Nat) (st : Nat × Bool) : Nat × Bool :=
  let s := sqs c k st
  (s.1 * powMod b d c % c,
    if d = 0 then s.2 else decide (s.1 * powMod b d c % c = 1) || decide (s.1 * powMod b d c % c = c - 1))

/-- The top `j` of the `W` windows of `k` bits of `E`, from `y = 1` and a
clear flag. -/
def kRun (k c b E W : Nat) : Nat → Nat × Bool
  | 0 => (1, false)
  | j + 1 => kWin k c b (E / (2 ^ k) ^ (W - 1 - j) % 2 ^ k) (kRun k c b E W j)

/-- The flag after the windows of `X`: clear for `X = 0`; for
`X = Y (2^k)^t` with `Y`'s low digit nonzero, `b^Y ≡ ±1` or one of the
`k t` squares after it is `c − 1`. -/
def FlagK (k c b X : Nat) (P : Bool) : Prop :=
  (X = 0 → P = false) ∧ ∀ Y t, X = Y * (2 ^ k) ^ t → Y % 2 ^ k ≠ 0 →
    (P = true ↔ (powMod b Y c = 1 ∨ powMod b Y c = c - 1 ∨
      ∃ i, 1 ≤ i ∧ i ≤ k * t ∧ sqIter c (powMod b Y c) i = c - 1))

theorem pow_pow2 (k t : Nat) : (2 ^ k) ^ t = 2 ^ (k * t) := by rw [← Nat.pow_mul]

/-- A window's power: `b^(2^k X + d) = (b^X)^(2^k) b^d`. -/
theorem powMod_kwin (k b X d c : Nat) (hk : 1 ≤ k) :
    powMod b (2 ^ k * X + d) c = sqIter c (powMod b X c) k * powMod b d c % c := by
  rw [sqIter_pow c _ k hk, VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq,
    VG.Proof.Bignum.powMod_eq, ← Nat.pow_mod, ← Nat.mul_mod, ← Nat.pow_mul, ← Nat.pow_add,
    Nat.mul_comm (2 ^ k) X]

theorem mul_pos_ne {Y t k : Nat} (hY : Y % 2 ^ k ≠ 0) : Y * (2 ^ k) ^ t ≠ 0 := by
  have : 0 < Y := Nat.pos_of_ne_zero fun h => hY (by subst h; simp)
  exact Nat.ne_of_gt (Nat.mul_pos this (Nat.pow_pos (Nat.two_pow_pos k)))

/-- One window. -/
theorem kwin_step {k c b X d : Nat} {P : Bool} (hk : 1 ≤ k) (hc : 3 ≤ c) (hd : d < 2 ^ k)
    (hF : FlagK k c b X P) :
    (kWin k c b d (powMod b X c, P)).1 = powMod b (2 ^ k * X + d) c ∧
    FlagK k c b (2 ^ k * X + d) (kWin k c b d (powMod b X c, P)).2 := by
  have hy : (kWin k c b d (powMod b X c, P)).1 = powMod b (2 ^ k * X + d) c := by
    simp only [kWin, sqs_fst]; exact (powMod_kwin k b X d c hk).symm
  refine ⟨hy, ?_⟩
  have hK : 0 < 2 ^ k := Nat.two_pow_pos k
  by_cases hd0 : d = 0
  · subst hd0
    have hP : (kWin k c b 0 (powMod b X c, P)).2 = (sqs c k (powMod b X c, P)).2 := by
      simp only [kWin, ↓reduceIte]
    rw [hP, Nat.add_zero]
    by_cases hX : X = 0
    · subst hX
      have hP0 := hF.1 rfl
      have hy1 : powMod b 0 c = 1 := powMod_zero' (by omega_arith)
      refine ⟨fun _ => ?_, fun Y t hYt hY => absurd (by rw [Nat.mul_zero] at hYt; exact hYt.symm)
        (mul_pos_ne (t := t) hY)⟩
      apply Bool.eq_false_iff.mpr
      intro h
      rw [sqs_snd] at h
      rcases h with h | ⟨i, _, _, hi⟩
      · rw [hP0] at h; cases h
      · simp only [hy1, sqIter_one c (by omega_arith)] at hi; omega_arith
    · refine ⟨fun h => absurd h (by
          have : 0 < 2 ^ k * X := Nat.mul_pos hK (Nat.pos_of_ne_zero hX)
          omega_arith), fun Y t hYt hY => ?_⟩
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := by
        rcases t with _ | t
        · exfalso
          rw [Nat.pow_zero, Nat.mul_one] at hYt
          subst hYt
          exact hY (Nat.mul_mod_right _ _)
        · exact ⟨t, rfl⟩
      have hXY : X = Y * (2 ^ k) ^ t := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (Y * (2 ^ k) ^ t) (2 ^ k)] at hYt
        exact Nat.eq_of_mul_eq_mul_left hK hYt
      have hYp : 0 < Y := Nat.pos_of_ne_zero fun h => hY (by subst h; simp)
      have hz : powMod b X c = sqIter c (powMod b Y c) (k * t) := by
        rw [hXY, pow_pow2]
        exact powMod_pow2 b Y c hYp (k * t)
      rw [sqs_snd, hF.2 Y t hXY hY]
      simp only [hz, ← sqIter_add]
      have e : k * (t + 1) = k * t + k := by rw [Nat.mul_succ]
      rw [e]
      constructor
      · rintro ((h | h | ⟨i, h1, h2, h3⟩) | ⟨i, h1, h2, h3⟩)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr ⟨i, h1, by omega_arith, h3⟩)
        · exact .inr (.inr ⟨k * t + i, by omega_arith, by omega_arith, h3⟩)
      · rintro (h | h | ⟨i, h1, h2, h3⟩)
        · exact .inl (.inl h)
        · exact .inl (.inr (.inl h))
        · rcases Nat.lt_or_ge (k * t) i with hi | hi
          · exact .inr ⟨i - k * t, by omega_arith, by omega_arith,
              by rw [Nat.add_sub_cancel' (Nat.le_of_lt hi)]; exact h3⟩
          · exact .inl (.inr (.inr ⟨i, h1, hi, h3⟩))
  · have hP : (kWin k c b d (powMod b X c, P)).2 =
        (decide (powMod b (2 ^ k * X + d) c = 1) || decide (powMod b (2 ^ k * X + d) c = c - 1)) := by
      rw [← hy]; simp only [kWin, hd0, ↓reduceIte]
    rw [hP]
    refine ⟨fun h => absurd h (by omega_arith), fun Y t hYt hY => ?_⟩
    have ht : t = 0 := by
      rcases t with _ | t
      · rfl
      · exfalso
        have h1 : (2 ^ k * X + d) % 2 ^ k = 0 := by
          rw [hYt, Nat.pow_succ, ← Nat.mul_assoc]; exact Nat.mul_mod_left _ _
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hd] at h1
        exact hd0 h1
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
      · omega_arith

/-- The windows so far: `y = b^X mod c` and the flag of `X`, for the top `X`
of `E`. -/
theorem kRun_ok {k c b E W : Nat} (hk : 1 ≤ k) (hc : 3 ≤ c) (hE : E < (2 ^ k) ^ W) : ∀ j, j ≤ W →
    (kRun k c b E W j).1 = powMod b (E / (2 ^ k) ^ (W - j)) c ∧
      FlagK k c b (E / (2 ^ k) ^ (W - j)) (kRun k c b E W j).2
  | 0, _ => by
    rw [Nat.sub_zero, Nat.div_eq_of_lt hE]
    exact ⟨(powMod_zero' (by omega_arith)).symm, fun _ => rfl, fun Y t hYt hY =>
      absurd hYt.symm (mul_pos_ne hY)⟩
  | j + 1, hj => by
    obtain ⟨hy, hF⟩ := kRun_ok hk hc hE j (by omega_arith)
    have e : E / (2 ^ k) ^ (W - (j + 1)) =
        2 ^ k * (E / (2 ^ k) ^ (W - j)) + E / (2 ^ k) ^ (W - 1 - j) % 2 ^ k := by
      rw [show W - j = (W - 1 - j) + 1 by omega_arith, show W - (j + 1) = W - 1 - j by omega_arith,
        Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      have := Nat.div_add_mod (E / (2 ^ k) ^ (W - 1 - j)) (2 ^ k)
      omega_arith
    rw [kRun, show kRun k c b E W j = (powMod b (E / (2 ^ k) ^ (W - j)) c, (kRun k c b E W j).2) by
      rw [← hy], e]
    exact kwin_step hk hc (Nat.mod_lt _ (Nat.two_pow_pos k)) hF

/-- The windows of `k` bits of `E` (`k` dividing 4) and the three squarings:
`mrIteration`'s result. -/
theorem kEnd_eq {k c W : Nat} (b : Nat) (hk : 1 ≤ k) (hk4 : 4 % k = 0) (hc : 3 ≤ c) (hodd : c % 2 = 1)
    (haw : mrA c ≤ bitLength c - 1) (hE : mrE c < (2 ^ k) ^ W) :
    (wEnd c (kRun k c b (mrE c) W W)).2 = mrIteration c (mrA c) (splitTwos (c - 1)).2 b := by
  obtain ⟨hN, hm2⟩ := splitTwos_spec (c - 1) (by omega_arith)
  change c - 1 = (splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  have hEd : mrE c = (c - 1) / 2 ^ sigOf (mrA c) := rfl
  have hsd : mrSig c = sigOf (mrA c) := rfl
  obtain ⟨hy, hF⟩ := kRun_ok (b := b) hk hc hE W (Nat.le_refl _)
  rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hy hF
  unfold wEnd
  generalize kRun k c b (mrE c) W W = st at hy hF
  obtain ⟨y, P⟩ := st
  simp only at hy hF ⊢
  rw [hsd]
  generalize hE' : mrE c = E at hy hF hEd
  generalize hm : (splitTwos (c - 1)).2 = m at hN hm2 ⊢
  generalize ha : mrA c = a at hN haw hEd ⊢
  subst hEd
  have hmp : 0 < m := by omega_arith
  have ha1 : 1 ≤ a := by
    rcases a with _ | a
    · rw [Nat.pow_zero, Nat.mul_one] at hN; omega_arith
    · omega_arith
  have hsig := sigOf_pos a
  have hσa := sigOf_le ha1
  obtain ⟨v, hv'⟩ : ∃ v, a - sigOf a = 4 * v := ⟨(a - sigOf a) / 4, by have := sigOf_sub (a := a); omega_arith⟩
  have has : 4 * v + sigOf a = a := by rw [← hv']; exact Nat.sub_add_cancel hσa
  obtain ⟨q, hq⟩ : ∃ q, 4 = k * q := ⟨4 / k, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk4)).symm⟩
  have hEm : (c - 1) / 2 ^ sigOf a = m * (2 ^ k) ^ (q * v) := by
    have h2 : 2 ^ a = 2 ^ (a - sigOf a) * 2 ^ sigOf a := by rw [← Nat.pow_add, Nat.sub_add_cancel hσa]
    rw [hN, h2, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _), hv', pow_pow2,
      ← Nat.mul_assoc, ← hq]
  rw [hEm] at hy hF
  have hmk : m % 2 ^ k ≠ 0 := by
    intro h
    have hd : 2 ∣ 2 ^ k := ⟨2 ^ (k - 1), by rw [← Nat.pow_succ']; congr 1; omega_arith⟩
    have := Nat.mod_mod_of_dvd m hd
    rw [h] at this
    omega_arith
  have hflag := hF.2 m (q * v) rfl hmk
  have hkv : k * (q * v) = 4 * v := by rw [← Nat.mul_assoc, ← hq]
  rw [hkv] at hflag
  have hyz : y = sqIter c (powMod b m c) (4 * v) := by
    rw [hy, pow_pow2, hkv]
    exact powMod_pow2 b m c hmp (4 * v)
  apply Bool.eq_iff_iff.mpr
  rw [wEnd_flag hsig.1 hsig.2 hflag hyz, mrIteration_iff hc ha1 haw, has]

end VG.Proof.MillerRabin.WindowK
