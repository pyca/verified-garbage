import VerifiedGarbage.Proof.Weierstrass.CombW

/-!
# A `w`-bit comb's digits from a table of bits, on any target

What the code of every target reads of a window of the scalar's bits, one
byte per bit: Horner's rule over the bytes (`hornerVal`) gives the window
(`hornerVal_eq`), `|k_j - H|` is its digit's magnitude (`magH`), and its top
bit says whether the digit is not negative (`testBit_top`).
-/

namespace VG.Proof.Weierstrass

/-- `Σ_{i<k} v (d + i) 2^i`. -/
def hornerVal (v : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | d, k + 1 => 2 * hornerVal v (d + 1) k + v d

theorem hornerVal_lt {v : Nat → Nat} (hv : ∀ i, v i ≤ 1) : ∀ d k, hornerVal v d k < 2 ^ k
  | _, 0 => Nat.one_pos
  | d, k + 1 => by
    have := hornerVal_lt hv (d + 1) k
    have := hv d
    simp only [hornerVal, Nat.pow_succ]; omega

/-- The window from its bits. -/
theorem hornerVal_eq (k w j : Nat) :
    ∀ i ≤ w, hornerVal (fun t => (k.testBit t).toNat) (w * j + (w - i)) i =
      k / 2 ^ (w * j + (w - i)) % 2 ^ i := by
  intro i
  induction i with
  | zero => intro _; simp [hornerVal, Nat.mod_one]
  | succ i ih =>
    intro hi
    have e := ih (by omega)
    rw [show w * j + (w - i) = w * j + (w - (i + 1)) + 1 by omega] at e
    simp only [hornerVal, e]
    generalize w * j + (w - (i + 1)) = t
    have hq : k / 2 ^ (t + 1) = k / 2 ^ t / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hb : (k.testBit t).toNat = k / 2 ^ t % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ t) with h | h <;> simp [h]
    rw [hq, hb, Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mod_mul]
    omega

/-- `|v - H|`, the magnitude of the digit of the window `v`. -/
def magH (H v : Nat) : Nat := if H ≤ v then v - H else H - v

theorem magH_le {H v : Nat} (hv : v < 2 * H) : magH H v ≤ H := by unfold magH; split <;> omega

/-- The window's top bit says whether its digit is not negative. -/
theorem testBit_top (k w j : Nat) (hw : 1 ≤ w) :
    k.testBit (w * j + (w - 1)) = decide (2 ^ (w - 1) ≤ combWin w k j) := by
  have hl := combWin_lt w k j
  rw [Nat.add_comm, ← Nat.testBit_div_two_pow, combWin]
  rw [show k / 2 ^ (w * j) = k / 2 ^ (w * j) % 2 ^ w + 2 ^ w * (k / 2 ^ (w * j) / 2 ^ w) from
    (Nat.mod_add_div _ _).symm]
  rw [combWin] at hl
  generalize k / 2 ^ (w * j) % 2 ^ w = r at hl ⊢
  generalize k / 2 ^ (w * j) / 2 ^ w = q
  have hw' : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [Nat.testBit_eq_decide_div_mod_eq, hw', Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have h2 : r / 2 ^ (w - 1) < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  rw [Nat.add_mul_mod_self_left]
  have hr : (r + 2 ^ (w - 1) * (2 * q)) % (2 ^ (w - 1) * 2) = r := by
    rw [← Nat.mul_assoc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [hr]
  by_cases h : 2 ^ (w - 1) ≤ r
  · have : r / 2 ^ (w - 1) = 1 := by
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega : 1 * 2 ^ (w - 1) ≤ r)
      omega
    simp [this, h]
  · have : r / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

theorem hornerVal_congr {v v' : Nat → Nat} : ∀ {d d' k : Nat}, (∀ i < k, v (d + i) = v' (d' + i)) →
    hornerVal v d k = hornerVal v' d' k
  | _, _, 0, _ => rfl
  | d, d', k + 1, h => by
    simp only [hornerVal]
    rw [hornerVal_congr (d := d + 1) (d' := d' + 1) (k := k) fun i hi => by
      rw [show d + 1 + i = d + (i + 1) by omega, show d' + 1 + i = d' + (i + 1) by omega]
      exact h (i + 1) (by omega)]
    have := h 0 (by omega)
    simp only [Nat.add_zero] at this
    rw [this]

end VG.Proof.Weierstrass
