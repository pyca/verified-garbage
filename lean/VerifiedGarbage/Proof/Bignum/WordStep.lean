import VerifiedGarbage.Proof.Bignum.Words

/-!
# Multiword arithmetic: a step of long division

The arithmetic of `x := x 2^64 mod m` by a step of long division (Knuth,
TAOCP vol. 2, §4.3.1, Algorithm D), for `R² mod m` by word steps
(`Impl/Bignum/X86_64/R2Words.lean`), independent of the target:

* the estimate `q̂ = min(⌊N / d⌋, 2^64 - 1)` of `q = ⌊y / m⌋` from the top two
  words `N` of `y` and the top word `d ≥ 2^63` of `m` is `q ≤ q̂ ≤ q + 2`
  (`qhat_ge`, `qhat_le`, Knuth's Theorem 4.3.1B);
* a bit of restoring division (`divBit_inv`);
* `y - q̂ m`, in two's complement modulo `W > 4 m`, with `m` added twice
  while it is negative, is `y mod m` (`addBack_two`).
-/

namespace VG.Proof.Bignum.WordStep

/-! ## The estimate of the quotient -/

/-- `q = ⌊y / m⌋ ≤ ⌊N / d⌋` for `y = N B + yₗ` and `m = d B + mₗ`, `yₗ < B`. -/
theorem quot_le_div {N yl ml B d : Nat} (hyl : yl < B) (hd : 0 < d) :
    (N * B + yl) / (d * B + ml) ≤ N / d := by
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) hyl
  rw [Nat.le_div_iff_mul_le hd]
  generalize hq : (N * B + yl) / (d * B + ml) = q
  have h1 : q * (d * B + ml) ≤ N * B + yl := hq ▸ Nat.div_mul_le_self _ _
  have h2 : q * d * B ≤ q * (d * B + ml) := by rw [Nat.mul_add, Nat.mul_assoc]; omega
  have h3 : q * d * B < (N + 1) * B := by rw [Nat.add_mul, Nat.one_mul]; omega
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h3)

/-- `⌊N / d⌋ ≤ q + 2` for `q = ⌊y / m⌋ < 2^64`, `y = N B + yₗ`,
`m = d B + mₗ`, `mₗ < B` and `2^63 ≤ d`. -/
theorem div_le_quot {N yl ml B d : Nat} (hml : ml < B) (hd : 2 ^ 63 ≤ d)
    (hq : (N * B + yl) / (d * B + ml) < 2 ^ 64) :
    N / d ≤ (N * B + yl) / (d * B + ml) + 2 := by
  generalize hqd : (N * B + yl) / (d * B + ml) = q at hq
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) hml
  have hM : 0 < d * B + ml := Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) hB) (Nat.le_add_right _ _)
  -- `y < (q + 1) m`.
  have hy : N * B + yl < (q + 1) * (d * B + ml) := by
    have := Nat.lt_mul_div_succ (N * B + yl) hM
    rw [hqd] at this
    rw [Nat.mul_comm (q + 1)]
    exact this
  rcases Nat.lt_or_ge (N / d) (q + 3) with h | h
  · omega
  · exfalso
    have hN : (q + 3) * d ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp h
    -- `(q + 3) d B ≤ y < (q + 1) m < (q + 1) (d + 1) B`.
    have h1 : (q + 3) * d * B ≤ N * B + yl := Nat.le_add_right_of_le (Nat.mul_le_mul_right B hN)
    have h2 : (q + 1) * (d * B + ml) < (q + 1) * ((d + 1) * B) :=
      Nat.mul_lt_mul_of_pos_left (by rw [Nat.add_mul, Nat.one_mul]; omega) (by omega)
    have h3 : (q + 3) * d * B < (q + 1) * (d + 1) * B := by rw [Nat.mul_assoc (q + 1)]; omega
    have h4 := Nat.lt_of_mul_lt_mul_right h3
    have e1 : (q + 3) * d = q * d + 3 * d := by rw [Nat.add_mul]
    have e2 : (q + 1) * (d + 1) = q * d + d + q + 1 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]; omega
    omega

/-- The estimate is at least the quotient. -/
theorem qhat_ge {N yl ml B d : Nat} (hyl : yl < B) (hd : 0 < d)
    (hq : (N * B + yl) / (d * B + ml) < 2 ^ 64) :
    (N * B + yl) / (d * B + ml) ≤ min (N / d) (2 ^ 64 - 1) :=
  Nat.le_min.mpr ⟨quot_le_div hyl hd, by omega⟩

/-- The estimate is at most the quotient plus 2. -/
theorem qhat_le {N yl ml B d : Nat} (hml : ml < B) (hd : 2 ^ 63 ≤ d)
    (hq : (N * B + yl) / (d * B + ml) < 2 ^ 64) :
    min (N / d) (2 ^ 64 - 1) ≤ (N * B + yl) / (d * B + ml) + 2 :=
  Nat.le_trans (Nat.min_le_left _ _) (div_le_quot hml hd hq)

/-! ## A bit of restoring division -/

/-- A bit `b` of the dividend, appended to the remainder `r < d` of
`P = q d + r`: `2 P + b = q' d + r'` with `r' < d`, for `r'` and `q'` as the
code chooses them by whether `2 r + b ≥ d`. -/
theorem divBit_inv {P q r d b : Nat} (hP : P = q * d + r) (hr : r < d) (hb : b < 2) :
    2 * P + b = (2 * q + if d ≤ 2 * r + b then 1 else 0) * d +
      (if d ≤ 2 * r + b then 2 * r + b - d else 2 * r + b) ∧
    (if d ≤ 2 * r + b then 2 * r + b - d else 2 * r + b) < d := by
  subst hP
  by_cases h : d ≤ 2 * r + b
  · simp only [h, ite_true]
    constructor
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]; omega
    · omega
  · simp only [h, ite_false, Nat.add_zero]
    constructor
    · rw [Nat.mul_assoc]; omega
    · omega

/-! ## The remainder, from `y - q̂ m` -/

/-- `v` modulo `W`, for an integer `v`. -/
def twos (W : Nat) (v : Int) : Nat := (v % (W : Int)).toNat

/-- `v` from its two's complement, for `-W / 2 ≤ v < W / 2`. -/
theorem twos_eq {W : Nat} {v : Int} (h1 : -((W : Int) / 2) ≤ v) (h2 : v < (W : Int) / 2) :
    (twos W v : Int) = if v < 0 then v + W else v := by
  unfold twos
  by_cases hv : v < 0
  · rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    simp only [hv, ite_true]; omega
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    simp only [hv, ite_false]; omega

/-- The sign of `v` from its two's complement: negative iff at least `W / 2`. -/
theorem twos_neg {W : Nat} {v : Int} (h1 : -((W : Int) / 2) ≤ v) (h2 : v < (W : Int) / 2) :
    (W / 2 ≤ twos W v ↔ v < 0) := by
  have := twos_eq h1 h2
  constructor
  · intro h; by_contra hv; simp only [hv, ite_false] at this; omega
  · intro hv; simp only [hv, ite_true] at this; omega

/-- A difference over the words, with its borrow `b`: `t + a = y + W b` is
the two's complement of `y - a`. -/
theorem twos_of_sub {W t a y b : Nat} (ht : t < W) (hb : b < 2) (h : t + a = y + W * b)
    (h1 : -((W : Int) / 2) ≤ (y : Int) - a) (h2 : (y : Int) - a < (W : Int) / 2) :
    t = twos W ((y : Int) - a) := by
  have e := twos_eq h1 h2
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
    by_cases hv : (y : Int) - a < 0 <;> simp only [hv, ite_true, ite_false] at e <;> omega

/-- `v`, with `m` added if it is negative. -/
def addIfNeg (m : Nat) (v : Int) : Int := v + if v < 0 then (m : Int) else 0

/-- A sum over the words, with its carry `c`: `t' + W c = t + a`, for `t` the
two's complement of `v` and `a = m` if it is negative (`0` otherwise), is the
two's complement of `v` with `m` added if negative. -/
theorem twos_of_add {W m t t' c : Nat} {v : Int} (h1 : -((W : Int) / 2) ≤ v)
    (h2 : v < (W : Int) / 2) (h1' : -((W : Int) / 2) ≤ addIfNeg m v) (h2' : addIfNeg m v < (W : Int) / 2)
    (ht : t = twos W v) (ht' : t' < W) (hc : c < 2)
    (h : t' + W * c = t + if W / 2 ≤ t then m else 0) : t' = twos W (addIfNeg m v) := by
  have e := twos_eq h1 h2
  have e' := twos_eq h1' h2'
  have hn := twos_neg h1 h2
  subst ht
  unfold addIfNeg at *
  by_cases hv : v < 0
  · have hc' : W / 2 ≤ twos W v := hn.mpr hv
    simp only [hc', ite_true, hv] at h e e' ⊢
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;>
      by_cases hv' : v + (m : Int) < 0 <;> simp only [hv', ite_true, ite_false] at e' <;> omega
  · have hc' : ¬ W / 2 ≤ twos W v := fun h' => hv (hn.mp h')
    simp only [hc', ite_false, hv, Nat.add_zero, Int.add_zero] at h e e' ⊢
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> omega

/-- `y - q̂ m`, for `q ≤ q̂ ≤ q + 2` (`q = ⌊y / m⌋`), with `m` added while it is
negative, twice: `y mod m`; and both values before an addition are within
`[-W / 2, W / 2)`, for `4 m < W / 2`. -/
theorem addBack_two {W y m qh : Nat} (hm : 0 < m) (hW : 4 * m < W / 2)
    (h1 : y / m ≤ qh) (h2 : qh ≤ y / m + 2) :
    addIfNeg m (addIfNeg m ((y : Int) - (qh * m : Nat))) = ((y % m : Nat) : Int) ∧
      -((W : Int) / 2) ≤ (y : Int) - (qh * m : Nat) ∧ (y : Int) - (qh * m : Nat) < (W : Int) / 2 ∧
      -((W : Int) / 2) ≤ addIfNeg m ((y : Int) - (qh * m : Nat)) ∧
      addIfNeg m ((y : Int) - (qh * m : Nat)) < (W : Int) / 2 := by
  have hy := Nat.div_add_mod y m
  have hr := Nat.mod_lt y hm
  obtain ⟨c, hc, hqm⟩ : ∃ c, c ≤ 2 ∧ qh * m = y / m * m + c * m :=
    ⟨qh - y / m, by omega, by rw [← Nat.add_mul]; congr 1; omega⟩
  have hyP : y = y / m * m + y % m := by rw [Nat.mul_comm]; omega
  rw [hqm]
  generalize y / m * m = P at *
  generalize y % m = r at *
  subst hyP
  unfold addIfNeg
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl <;>
    (try simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero]) <;> push_cast <;> by_cases ha : (P : Int) + r - P < 0 <;> by_cases hb : (P : Int) + r - (P + m) < 0 <;> by_cases hc : (P : Int) + r - (P + 2 * m) < 0 <;> simp_all <;> omega

/-! ## The step -/

/-- A step of long division over the words, as `R2Words.step` makes it: for
`x < m` of `w ≥ 2` words, `m`'s top word `d ≥ 2^63`, `q̂` the estimate from
the top words `u₂`, `u₁` of `x`, `t₁ = x 2^64 - q̂ m` modulo `W = 2^(64 (w + 1))`
(with its borrow `b`) and `m` added twice to it while its top half is set
(with the carries `c₁`, `c₂`): `x 2^64 mod m`. -/
theorem wordStep_val {w X M u2 u1 Xl d ml T1 T2 T3 b c1 c2 : Nat} (hw : 2 ≤ w)
    (hX : X = u2 * 2 ^ (64 * (w - 1)) + u1 * 2 ^ (64 * (w - 2)) + Xl) (hXl : Xl < 2 ^ (64 * (w - 2)))
    (hM : M = d * 2 ^ (64 * (w - 1)) + ml) (hml : ml < 2 ^ (64 * (w - 1)))
    (hd : 2 ^ 63 ≤ d) (hd' : d < 2 ^ 64) (hXM : X < M)
    (hT1 : T1 < 2 ^ (64 * (w + 1))) (hb : b < 2)
    (h1 : T1 + min ((u2 * 2 ^ 64 + u1) / d) (2 ^ 64 - 1) * M = X * 2 ^ 64 + 2 ^ (64 * (w + 1)) * b)
    (hT2 : T2 < 2 ^ (64 * (w + 1))) (hc1 : c1 < 2)
    (h2 : T2 + 2 ^ (64 * (w + 1)) * c1 = T1 + if 2 ^ (64 * (w + 1)) / 2 ≤ T1 then M else 0)
    (hT3 : T3 < 2 ^ (64 * (w + 1))) (hc2 : c2 < 2)
    (h3 : T3 + 2 ^ (64 * (w + 1)) * c2 = T2 + if 2 ^ (64 * (w + 1)) / 2 ≤ T2 then M else 0) :
    T3 = X * 2 ^ 64 % M := by
  generalize hW : 2 ^ (64 * (w + 1)) = W at *
  have hB : 2 ^ (64 * (w - 1)) = 2 ^ (64 * (w - 2)) * 2 ^ 64 := by
    rw [show 64 * (w - 1) = 64 * (w - 2) + 64 by omega, Nat.pow_add]
  have hWB : W = 2 ^ (64 * (w - 1)) * 2 ^ 64 * 2 ^ 64 := by
    rw [← hW, show 64 * (w + 1) = 64 * (w - 1) + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
  generalize 2 ^ (64 * (w - 1)) = B at *
  have hM0 : 0 < M := by omega
  -- `x 2^64 = (u₂ 2^64 + u₁) B + xₗ 2^64`, with `xₗ 2^64 < B`.
  have hY : X * 2 ^ 64 = (u2 * 2 ^ 64 + u1) * B + Xl * 2 ^ 64 := by rw [hX, hB]; grind
  have hYl : Xl * 2 ^ 64 < B := by rw [hB]; exact Nat.mul_lt_mul_of_pos_right hXl (Nat.two_pow_pos 64)
  -- `q < 2^64`.
  have hq : X * 2 ^ 64 / M < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul hM0, Nat.mul_comm (2 ^ 64) M]; exact Nat.mul_lt_mul_of_pos_right hXM (Nat.two_pow_pos 64)
  rw [hY, hM] at hq
  have hge := qhat_ge hYl (by omega) hq
  have hle := qhat_le hml hd hq
  rw [← hY, ← hM] at hge hle
  generalize min ((u2 * 2 ^ 64 + u1) / d) (2 ^ 64 - 1) = qh at *
  -- `4 m < W / 2`.
  have hMW : 4 * M < W / 2 := by
    have : M < B * 2 ^ 64 := by
      have := Nat.mul_le_mul_right B (show d + 1 ≤ 2 ^ 64 by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ 64)] at this
      rw [hM]; omega
    rw [hWB]; omega
  obtain ⟨hfin, hv1, hv2, hw1, hw2⟩ := addBack_two (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega) hv1 hv2
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc1 h2
  have hv1' : -((W : Int) / 2) ≤ addIfNeg M (addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat))) := by
    rw [hfin]; omega
  have hv2' : addIfNeg M (addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat))) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt (X * 2 ^ 64) hM0; omega
  have e3 := twos_of_add hw1 hw2 hv1' hv2' e2 hT3 hc2 h3
  rw [e3, hfin]
  have hr := Nat.mod_lt (X * 2 ^ 64) hM0
  have hMW' : M < W := Nat.lt_of_lt_of_le (by omega) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

end VG.Proof.Bignum.WordStep
