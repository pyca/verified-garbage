module
public import VerifiedGarbage.Proof.Framework.PowLit


/-!
# Montgomery multiplication without a reduced operand

With operands below `R = 2^(64 w)` but not below `m`, the accumulator of the
rounds stays below `m + b` (`round_lt_add`), and the reduction of a product
`X < R²` is below `R + m`. One subtraction of `m` then leaves a result below
`R`: when it does not borrow (`csub_lazy`), or when the word above `R` is set
(`lazy_sub`, the mask's subtraction).
-/

@[expose] public section

namespace VG.Proof.Bignum

/-- A round keeps the accumulator below `m + b`, for any `b`. -/
theorem round_lt_add {T T' a b u m : Nat} (h : 2 ^ 64 * T' = T + a * b + u * m) (hT : T < m + b)
    (ha : a < 2 ^ 64) (hu : u < 2 ^ 64) : T' < m + b := by
  have h1 : a * b ≤ (2 ^ 64 - 1) * b := Nat.mul_le_mul_right _ (by omega)
  have h2 : u * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.sub_mul, Nat.one_mul] at h1 h2
  have : 2 ^ 64 * T' < 2 ^ 64 * (m + b) := by
    rw [h, Nat.mul_add]; omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- The reduction `(X + q m) / R` of `X < R R`, for `q < R`, is below `R + m`. -/
theorem redc_lt_add {R T X q m : Nat} (hq : q < R) (hX : X < R * R) (he : R * T = X + q * m) :
    T < R + m := by
  have hqm : q * m ≤ (R - 1) * m := Nat.mul_le_mul_right _ (by omega)
  have : R * T < R * (R + m) := by
    rw [he, Nat.mul_add]
    have : (R - 1) * m + m = R * m := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega))]
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- `csub_result` for `T < m + R`: what `subMod` and `selectAcc` leave is
below `R` and congruent to `T` modulo `m`. -/
theorem csub_lazy {Tl Tw Tw1 D m R c : Nat} (hm : m < R) (hD : D < R) (hc : c ≤ 1)
    (hTl : Tl < R) (hT : Tl + R * (Tw + 2 ^ 64 * Tw1) < m + R) (hsub : D + m = Tl + R * c) :
    (if Tw < c then Tl else D) < R ∧
      (if Tw < c then Tl else D) % m = (Tl + R * (Tw + 2 ^ 64 * Tw1)) % m := by
  have hR : 0 < R := by omega
  have h1 : Tw1 = 0 := by
    rcases Nat.eq_zero_or_pos Tw1 with h | h
    · exact h
    · have : R * 2 ^ 64 ≤ R * (Tw + 2 ^ 64 * Tw1) := Nat.mul_le_mul_left _ (by
        have := Nat.mul_le_mul_left (2 ^ 64) h; omega)
      have : R * 2 ^ 64 ≥ 2 * R := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by decide)
      omega
  subst h1
  simp only [Nat.mul_zero, Nat.add_zero] at hT ⊢
  rcases Nat.lt_or_ge Tw 1 with hw | hw
  · have hw0 : Tw = 0 := by omega
    subst hw0
    simp only [Nat.mul_zero, Nat.add_zero] at hT ⊢
    rcases Nat.lt_or_ge c 1 with hc0 | hc1
    · have : c = 0 := by omega
      subst this
      simp only [Nat.lt_irrefl, ite_false]
      simp only [Nat.mul_zero, Nat.add_zero] at hsub
      refine ⟨hD, ?_⟩
      rw [show Tl = D + m by omega, Nat.add_mod_right]
    · have : c = 1 := by omega
      subst this
      simp only [Nat.zero_lt_one, ite_true]
      exact ⟨hTl, trivial⟩
  · have : R * 1 ≤ R * Tw := Nat.mul_le_mul_left _ hw
    have hw1 : Tw = 1 := by
      rcases Nat.lt_or_ge Tw 2 with h | h
      · omega
      · have : R * 2 ≤ R * Tw := Nat.mul_le_mul_left _ h
        omega
    subst hw1
    have hc1 : c = 1 := by
      rcases Nat.lt_or_ge c 1 with h | h
      · have : c = 0 := by omega
        subst this; omega
      · omega
    subst hc1
    simp only [Nat.lt_irrefl, ite_false, Nat.mul_one] at hsub ⊢
    refine ⟨hD, ?_⟩
    rw [show Tl + R = D + m by omega, Nat.add_mod_right]

/-- The masked subtraction: for `T = T_l + R T_w < R + m` (`T_l < R`,
`T_w ≤ 1`) and `o + (T_w m) = T_l + R c` (`o < R`, `c` the borrow), `o` is
congruent to `T` modulo `m`. -/
theorem lazy_sub {Tl Tw o m R c : Nat} (ho : o < R) (hc : c ≤ 1)
    (hTw : Tw ≤ 1) (hT : Tl + R * Tw < R + m) (hsub : o + Tw * m = Tl + R * c) :
    o % m = (Tl + R * Tw) % m := by
  rcases Nat.lt_or_ge Tw 1 with hw | hw
  · have : Tw = 0 := by omega
    subst this
    simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at hsub ⊢
    rcases Nat.lt_or_ge c 1 with hc0 | hc1
    · have : c = 0 := by omega
      subst this
      simp only [Nat.mul_zero, Nat.add_zero] at hsub
      rw [hsub]
    · have : R * 1 ≤ R * c := Nat.mul_le_mul_left _ hc1
      omega
  · have : Tw = 1 := by omega
    subst this
    simp only [Nat.one_mul, Nat.mul_one] at hsub hT ⊢
    rcases Nat.lt_or_ge c 1 with hc0 | hc1
    · have : c = 0 := by omega
      subst this
      omega
    · have : c = 1 := by omega
      subst this
      simp only [Nat.mul_one] at hsub
      rw [show Tl + R = o + m by omega, Nat.add_mod_right]

end VG.Proof.Bignum
