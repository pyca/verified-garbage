import VerifiedGarbage.Proof.Bignum.Words

/-!
# Multiword arithmetic: a step of long division

The arithmetic of `x := x 2^64 mod m` by a step of long division (Knuth,
TAOCP vol. 2, §4.3.1, Algorithm D), for `R² mod m` by word steps
(`Impl/Bignum/X86_64/R2Words.lean`), independent of the target:

* the estimate `q̂ = min(⌊N / d⌋, 2^64 - 1)` of `q = ⌊y / m⌋` from the top two
  words `N` of `y` and the top word `d ≥ 2^63` of `m` is `q ≤ q̂ ≤ q + 2`
  (`qhat_ge`, `qhat_le`, Knuth's Theorem 4.3.1B);
* the quotient `⌊N / d⌋` for `N < d 2^64` by Möller and Granlund's division
  by the reciprocal of `d` (`mg_quot`);
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
  have h2 : q * d * B ≤ q * (d * B + ml) := by rw [Nat.mul_add, Nat.mul_assoc]; omega_using []
  have h3 : q * d * B < (N + 1) * B := by rw [Nat.add_mul, Nat.one_mul]; omega_using [hyl, h1, h2]
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h3)

/-- `⌊N / d⌋ ≤ q + 2` for `q = ⌊y / m⌋ < 2^64`, `y = N B + yₗ`,
`m = d B + mₗ`, `mₗ < B` and `2^63 ≤ d`. -/
theorem div_le_quot {N yl ml B d : Nat} (hml : ml < B) (hd : 2 ^ 63 ≤ d)
    (hq : (N * B + yl) / (d * B + ml) < 2 ^ 64) :
    N / d ≤ (N * B + yl) / (d * B + ml) + 2 := by
  generalize hqd : (N * B + yl) / (d * B + ml) = q at hq
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) hml
  have hM : 0 < d * B + ml := Nat.lt_of_lt_of_le (Nat.mul_pos (by omega_using [hd]) hB) (Nat.le_add_right _ _)
  -- `y < (q + 1) m`.
  have hy : N * B + yl < (q + 1) * (d * B + ml) := by
    have := Nat.lt_mul_div_succ (N * B + yl) hM
    rw [hqd] at this
    rw [Nat.mul_comm (q + 1)]
    exact this
  rcases Nat.lt_or_ge (N / d) (q + 3) with h | h
  · omega_using [h]
  · exfalso
    have hN : (q + 3) * d ≤ N := (Nat.le_div_iff_mul_le (by omega_using [hd])).mp h
    -- `(q + 3) d B ≤ y < (q + 1) m < (q + 1) (d + 1) B`.
    have h1 : (q + 3) * d * B ≤ N * B + yl := Nat.le_add_right_of_le (Nat.mul_le_mul_right B hN)
    have h2 : (q + 1) * (d * B + ml) < (q + 1) * ((d + 1) * B) :=
      Nat.mul_lt_mul_of_pos_left (by rw [Nat.add_mul, Nat.one_mul]; omega_using [hml]) (by omega_using [])
    have h3 : (q + 3) * d * B < (q + 1) * (d + 1) * B := by rw [Nat.mul_assoc (q + 1)]; omega_using [hy, h1, h2]
    have h4 := Nat.lt_of_mul_lt_mul_right h3
    have e1 : (q + 3) * d = q * d + 3 * d := by rw [Nat.add_mul]
    have e2 : (q + 1) * (d + 1) = q * d + d + q + 1 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]; omega_using []
    omega_using [hd, hq, h4, e1, e2]

/-- The estimate is at least the quotient. -/
theorem qhat_ge {N yl ml B d : Nat} (hyl : yl < B) (hd : 0 < d)
    (hq : (N * B + yl) / (d * B + ml) < 2 ^ 64) :
    (N * B + yl) / (d * B + ml) ≤ min (N / d) (2 ^ 64 - 1) :=
  Nat.le_min.mpr ⟨quot_le_div hyl hd, by omega_using [hq]⟩

/-- The estimate is at most the quotient plus 2. -/
theorem qhat_le {N yl ml B d : Nat} (hml : ml < B) (hd : 2 ^ 63 ≤ d)
    (hq : (N * B + yl) / (d * B + ml) < 2 ^ 64) :
    min (N / d) (2 ^ 64 - 1) ≤ (N * B + yl) / (d * B + ml) + 2 :=
  Nat.le_trans (Nat.min_le_left _ _) (div_le_quot hml hd hq)

/-! ## Division by the reciprocal -/

/-- The bounds of Möller and Granlund's candidate remainder `T - (q₁ + 1) d`. -/
theorem mg_bounds {B d q0 u a K T q1 : Nat} (hd : d < B) (hq0B : q0 < B)
    (hu : u + 1 ≤ d) (hK : K ≤ d) (ha : a < B) (h1 : 0 < d) (h2 : 0 < B)
    (hid : (B : Int) * T + ((B : Int) - q0) * d = u * K + a * ((B : Int) - d) + B * (q1 + 1) * d) :
    q0 + (q1 + 1) * d < T + B ∧ (q1 + 1) * d ≤ T + d ∧
      (T < (q1 + 1) * d + (B - d) ∨ T < (q1 + 1) * d + q0) := by
  have e : ((q1 + 1) * d : Nat) = ((q1 : Int) + 1) * d := by
    rw [Int.natCast_mul, Int.natCast_add]; rfl
  have p0 : (0 : Int) ≤ u * K := Int.mul_nonneg (by omega_using []) (by omega_using [])
  have p0' : (0 : Int) ≤ a * ((B : Int) - d) := Int.mul_nonneg (by omega_using []) (by omega_using [hd])
  have pB : ((B : Int) - q0) * d < ((B : Int) - q0) * B := Int.mul_lt_mul_of_pos_left (by omega_using [hd]) (by omega_using [hq0B])
  have pB' : ((B : Int) - q0) * d ≤ (B : Int) * d := Int.mul_le_mul_of_nonneg_right (by omega_using []) (by omega_using [])
  refine ⟨?_, ?_, ?_⟩
  · have : (B : Int) * ((q0 : Int) + ((q1 : Int) + 1) * d) < B * (T + B) := by grind
    have := Int.lt_of_mul_lt_mul_left this (by omega_using [])
    omega_using [e, this]
  · have : (B : Int) * (((q1 : Int) + 1) * d) ≤ B * (T + d) := by grind
    have := Int.le_of_mul_le_mul_left this (by omega_using [h2])
    omega_using [e, this]
  · rcases Nat.lt_or_ge T ((q1 + 1) * d + (B - d)) with h | hc1
    · exact Or.inl h
    rcases Nat.lt_or_ge T ((q1 + 1) * d + q0) with h | hc2
    · exact Or.inr h
    exfalso
    replace hc1 : (B : Int) - d + ((q1 : Int) + 1) * d ≤ T := by omega_using [e, hc1]
    replace hc2 : (q0 : Int) + ((q1 : Int) + 1) * d ≤ T := by omega_using [e, hc2]
    generalize hρ : (T : Int) - ((q1 : Int) + 1) * d = ρ at *
    have p1 : (u : Int) * K ≤ ((d : Int) - 1) * d := Int.mul_le_mul (by omega_using [hu]) (by omega_using [hK])
        (by omega_using []) (by omega_using [h1])
    have p2 : (a : Int) * ((B : Int) - d) ≤ ((B : Int) - 1) * ((B : Int) - d) :=
      Int.mul_le_mul_of_nonneg_right (by omega_using [ha]) (by omega_using [hd])
    have p3 : ((B : Int) - d) * ((B : Int) - d) ≤ ρ * ((B : Int) - d) :=
      Int.mul_le_mul_of_nonneg_right (by omega_using [hc1, hρ]) (by omega_using [hd])
    have p4 : (q0 : Int) * d ≤ ρ * d := Int.mul_le_mul_of_nonneg_right (by omega_using [hc2, hρ]) (by omega_using [])
    have hT : (T : Int) = ρ + ((q1 : Int) + 1) * d := by omega_using [hρ]
    rw [hT] at hid
    grind

/-- Möller and Granlund's division of `u 2^64 + a` by `d ≥ 2^63`, for `u < d`,
by the reciprocal `V - 2^64` for `V = ⌊(2^128 - 1) / d⌋` ("Improved division
by invariant integers", IEEE Trans. Computers 60(2), 2011, Algorithm 4):
`(q₁, q₀) = V u + a`, the candidate `Q = q₁ + 1` and its remainder
`r = a - Q d` modulo `2^64`; then `Q - 1` and `r + d` if `r > q₀`, and one
more if then `r ≥ d`. -/
theorem mg_quot {d u a V P Q r Q1 r1 : Nat}
    (hd : d < 2 ^ 64) (hn : 2 ^ 63 ≤ d) (hu : u < d) (ha : a < 2 ^ 64)
    (hV : V = (2 ^ 128 - 1) / d) (hP : P = V * u + a)
    (hQ : Q = (P / 2 ^ 64 + 1) % 2 ^ 64)
    (hr : r = (a + (2 ^ 64 - Q * d % 2 ^ 64)) % 2 ^ 64)
    (hQ1 : Q1 = (Q + if P % 2 ^ 64 < r then 2 ^ 64 - 1 else 0) % 2 ^ 64)
    (hr1 : r1 = (r + if P % 2 ^ 64 < r then d else 0) % 2 ^ 64) :
    (Q1 + if d - 1 < r1 then 1 else 0) % 2 ^ 64 = (u * 2 ^ 64 + a) / d := by
  have hd0 : 0 < d := by omega_using [hu]
  -- `V d + k = 2^128`, `1 ≤ k ≤ d`.
  have hVd : V * d ≤ 2 ^ 128 - 1 := hV ▸ Nat.div_mul_le_self _ _
  have hVd' : 2 ^ 128 - 1 < V * d + d := by
    have := Nat.lt_mul_div_succ (2 ^ 128 - 1) hd0
    rw [← hV, Nat.mul_add, Nat.mul_one, Nat.mul_comm d V] at this; exact this
  -- `V ≥ 2^64`, so `P < 2^128`.
  have hVB : 2 ^ 64 ≤ V := by
    rw [hV, Nat.le_div_iff_mul_le hd0]
    have := Nat.mul_le_mul_left (2 ^ 64) (show d ≤ 2 ^ 64 - 1 by omega_using [hd])
    omega_using [this]
  have hVu : V * u + V ≤ V * d := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hu
  have hPB : P < 2 ^ 128 := by omega_using [ha, hP, hVd, hVB, hVu]
  generalize hq1 : P / 2 ^ 64 = q1 at hQ
  generalize hq0 : P % 2 ^ 64 = q0 at hQ1 hr1
  have hP2 : P = q1 * 2 ^ 64 + q0 := by
    have := Nat.div_add_mod P (2 ^ 64); rw [hq1, hq0] at this; omega_using [this]
  have hq0B : q0 < 2 ^ 64 := hq0 ▸ Nat.mod_lt _ (by decide)
  have hq1B : q1 < 2 ^ 64 := by rw [← hq1, Nat.div_lt_iff_lt_mul (by decide)]; omega_using [hPB]
  -- The quotient and remainder.
  generalize hT : u * 2 ^ 64 + a = T
  generalize hq : T / d = q
  generalize hρ : T % d = ρ
  have hTq : T = q * d + ρ := by
    have := Nat.div_add_mod T d; rw [hq, hρ, Nat.mul_comm] at this; omega_using [this]
  have hρd : ρ < d := hρ ▸ Nat.mod_lt _ hd0
  have hqB : q < 2 ^ 64 := by
    rw [← hq, Nat.div_lt_iff_lt_mul hd0]
    have := Nat.mul_le_mul_right (2 ^ 64) (show u + 1 ≤ d by omega_using [hu])
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm]; omega_using [ha, hT, this]
  -- `2^64 (T - (q₁ + 1) d) = u k + a (2^64 - d) - (2^64 - q₀) d`.
  have hid : (2 ^ 64 : Int) * T + ((2 ^ 64 - q0 : Nat) : Int) * d =
      u * ((2 ^ 128 - V * d : Nat) : Int) + a * ((2 ^ 64 - d : Nat) : Int) + 2 ^ 64 * (q1 + 1) * d := by
    have e1 : (P : Int) = V * u + a := by rw [hP, Int.natCast_add, Int.natCast_mul]
    have e2 : (P : Int) = q1 * 2 ^ 64 + q0 := by
      rw [hP2, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]; rfl
    have e3 : (T : Int) = u * 2 ^ 64 + a := by
      rw [← hT, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]; rfl
    have e4 : ((2 ^ 128 - V * d : Nat) : Int) = 2 ^ 128 - V * d := by
      rw [Int.natCast_sub (by omega_using [hVd]), Int.natCast_mul, Int.natCast_pow]; rfl
    have e5 : ((2 ^ 64 - q0 : Nat) : Int) = 2 ^ 64 - q0 := by
      rw [Int.natCast_sub (by omega_using [hq0B]), Int.natCast_pow]; rfl
    have e6 : ((2 ^ 64 - d : Nat) : Int) = 2 ^ 64 - d := by
      rw [Int.natCast_sub (by omega_using [hd]), Int.natCast_pow]; rfl
    grind
  generalize hK : 2 ^ 128 - V * d = K at hid
  have hK1 : 1 ≤ K := by omega_using [hVd, hK]
  have hKd : K ≤ d := by omega_using [hVd', hK]
  -- The bounds: `q₀ - 2^64 < T - (q₁ + 1) d`, `-d ≤ T - (q₁ + 1) d` and
  -- `T - (q₁ + 1) d < max(2^64 - d, q₀)`.
  have hb := mg_bounds (B := 2 ^ 64) (d := d) (q0 := q0) (u := u) (a := a) (K := K) (T := T) (q1 := q1)
    (by omega_using [hd]) (by omega_using [hq0B]) (by omega_using [hu]) (by omega_using [hKd]) (by omega_using [ha])
        (by omega_using [hK1, hKd]) (by omega_using [])
    (by
      have e64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by rw [Int.natCast_pow]; rfl
      rw [Int.natCast_sub (by omega_using [hq0B]), Int.natCast_sub (by omega_using [hd])] at hid
      simp only [e64] at hid ⊢; exact hid)
  generalize hD : (q1 + 1) * d = D at hb
  have hDe : D = q1 * d + d := by rw [← hD, Nat.succ_mul]
  obtain ⟨hL, hL2, hU⟩ := hb
  -- `q` is `q₁`, `q₁ + 1` or `q₁ + 2`.
  have hcase : (q = q1 ∧ D = q * d + d) ∨ (q = q1 + 1 ∧ D = q * d) ∨ (q = q1 + 2 ∧ q * d = D + d) := by
    rcases Nat.lt_or_ge q q1 with h | h
    · exfalso
      have := Nat.mul_le_mul_right d (show q + 1 ≤ q1 by omega_using [h])
      rw [Nat.succ_mul] at this; omega_using [hTq, hρd, hDe, hL2, this]
    rcases Nat.lt_or_ge q (q1 + 3) with h' | h'
    · rcases (show q = q1 ∨ q = q1 + 1 ∨ q = q1 + 2 by omega_using [h, h']) with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, by omega_using [hDe]⟩
      · exact Or.inr (Or.inl ⟨rfl, by rw [← hD]⟩)
      · exact Or.inr (Or.inr ⟨rfl, by rw [← hD, ← Nat.succ_mul]⟩)
    · exfalso
      have := Nat.mul_le_mul_right d h'
      rw [show q1 + 3 = (q1 + 1) + 2 by omega_using [], Nat.add_mul, hD] at this
      omega_using [hn, hq0B, hTq, hU, this]
  -- `Q d`.
  have hQd : Q * d = if q1 + 1 < 2 ^ 64 then D else 0 := by
    rw [hQ]
    by_cases h : q1 + 1 < 2 ^ 64
    · simp only [Nat.mod_eq_of_lt h, h, ite_true, hD]
    · simp only [h, ite_false]
      rw [show q1 + 1 = 2 ^ 64 by omega_using [hqB, hcase, h], Nat.mod_self, Nat.zero_mul]
  have hQv : Q = (q1 + 1) % 2 ^ 64 := hQ
  clear hV hP hVd hVd' hVB hVu hPB hq1 hq0 hP2 hK hK1 hKd hρ hq hid hD
  subst hQ1 hr1 hr
  rcases hcase with ⟨rfl, hDq⟩ | ⟨rfl, hDq⟩ | ⟨rfl, hDq⟩
  · -- `T - (q₁ + 1) d < 0`: both corrections.
    have hwrap : ¬ q + 1 < 2 ^ 64 → D = 2 ^ 64 * d := fun h => by
      have := Nat.succ_mul q d
      rw [show q.succ = 2 ^ 64 by omega_using [hq1B, h]] at this; omega_using [hDe, this]
    have hm : q0 < (a + (2 ^ 64 - Q * d % 2 ^ 64)) % 2 ^ 64 := by
      rw [hQd]; split
      · omega_using [hT, hTq, hρd, hL, hDe]
      · have := hwrap ‹_›; omega_using [hT, hTq, hρd, hL, hDe, this]
    rw [ite_eq_left hm, ite_eq_left hm]
    have hm' : ¬ d - 1 < ((a + (2 ^ 64 - Q * d % 2 ^ 64)) % 2 ^ 64 + d) % 2 ^ 64 := by
      rw [hQd]; split
      · omega_using [hT, hTq, hρd, hDe]
      · have := hwrap ‹_›; omega_using [hT, hTq, hρd, hDe, this]
    rw [ite_eq_right hm']
    omega_using [hq1B, hQv]
  · -- `0 ≤ T - (q₁ + 1) d < d`: none, or both.
    have hr : (a + (2 ^ 64 - Q * d % 2 ^ 64)) % 2 ^ 64 = ρ := by
      rw [hQd, ite_eq_left (by omega_using [hqB])]; omega_using [hq0B, hT, hU, hTq, hDq]
    rw [hr]
    by_cases hm : q0 < ρ
    · have hm' : d - 1 < (ρ + d) % 2 ^ 64 := by omega_using [hU, hTq, hDq, hm]
      rw [ite_eq_left hm, ite_eq_left hm, ite_eq_left hm']
      omega_using [hQv, hqB]
    · have hm' : ¬ d - 1 < ρ % 2 ^ 64 := by omega_arith
      rw [ite_eq_right hm, ite_eq_right hm, Nat.add_zero, Nat.add_zero, ite_eq_right hm']
      omega_arith
  · -- `d ≤ T - (q₁ + 1) d`: the second.
    have hr : (a + (2 ^ 64 - Q * d % 2 ^ 64)) % 2 ^ 64 = ρ + d := by
      rw [hQd, ite_eq_left (by omega_arith)]; omega_arith
    rw [hr]
    have hm : ¬ q0 < ρ + d := by omega_arith
    have hm' : d - 1 < (ρ + d) % 2 ^ 64 := by omega_arith
    rw [ite_eq_right hm, ite_eq_right hm, Nat.add_zero, Nat.add_zero, ite_eq_left hm']
    omega_arith

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
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]; omega_using [h]
    · omega_using [hr, hb]
  · simp only [h, ite_false, Nat.add_zero]
    constructor
    · rw [Nat.mul_assoc]; omega_using []
    · omega_using [h]

/-! ## The remainder, from `y - q̂ m` -/

/-- `v` modulo `W`, for an integer `v`. -/
def twos (W : Nat) (v : Int) : Nat := (v % (W : Int)).toNat

/-- `v` from its two's complement, for `-W / 2 ≤ v < W / 2`. -/
theorem twos_eq {W : Nat} {v : Int} (h1 : -((W : Int) / 2) ≤ v) (h2 : v < (W : Int) / 2) :
    (twos W v : Int) = if v < 0 then v + W else v := by
  unfold twos
  by_cases hv : v < 0
  · rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega_using [h1]) (by omega_using [hv])]
    simp only [hv, ite_true]; omega_using [h1]
  · rw [Int.emod_eq_of_lt (by omega_using [hv]) (by omega_using [h2])]
    simp only [hv, ite_false]; omega_using [hv]

/-- The sign of `v` from its two's complement: negative iff at least `W / 2`. -/
theorem twos_neg {W : Nat} {v : Int} (h1 : -((W : Int) / 2) ≤ v) (h2 : v < (W : Int) / 2) :
    (W / 2 ≤ twos W v ↔ v < 0) := by
  have := twos_eq h1 h2
  constructor
  · intro h; by_contra hv; simp only [hv, ite_false] at this; omega_using [h2, h, this]
  · intro hv; simp only [hv, ite_true] at this; omega_using [h1, this]

/-- A difference over the words, with its borrow `b`: `t + a = y + W b` is
the two's complement of `y - a`. -/
theorem twos_of_sub {W t a y b : Nat} (ht : t < W) (hb : b < 2) (h : t + a = y + W * b)
    (h1 : -((W : Int) / 2) ≤ (y : Int) - a) (h2 : (y : Int) - a < (W : Int) / 2) :
    t = twos W ((y : Int) - a) := by
  have e := twos_eq h1 h2
  rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;>
    by_cases hv : (y : Int) - a < 0 <;> simp only [hv, ite_true, ite_false] at e <;> omega_using [h, hv, e, ht]

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
    rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl <;>
      by_cases hv' : v + (m : Int) < 0 <;> simp only [hv', ite_true, ite_false] at e' <;> omega_using [e, h, e', ht', hv']
  · have hc' : ¬ W / 2 ≤ twos W v := fun h' => hv (hn.mp h')
    simp only [hc', ite_false, hv, Nat.add_zero, Int.add_zero] at h e e' ⊢
    rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl <;> omega_using [h, hc']

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
    ⟨qh - y / m, by omega_using [h2], by rw [← Nat.add_mul]; congr 1; omega_using [h1]⟩
  have hyP : y = y / m * m + y % m := by rw [Nat.mul_comm]; omega_using [hy]
  rw [hqm]
  generalize y / m * m = P at *
  generalize y % m = r at *
  subst hyP
  unfold addIfNeg
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega_using [hc]) with rfl | rfl | rfl <;>
    (try simp only [Nat.zero_mul, Nat.one_mul,
        Nat.add_zero]) <;> push_cast <;> by_cases ha : (P : Int) + r - P < 0 <;> by_cases hb : (P : Int) + r - (P + m) < 0 <;> by_cases hc : (P : Int) + r - (P + 2 * m) < 0 <;> simp_all <;> omega_arith

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
    rw [show 64 * (w - 1) = 64 * (w - 2) + 64 by omega_using [hw], Nat.pow_add]
  have hWB : W = 2 ^ (64 * (w - 1)) * 2 ^ 64 * 2 ^ 64 := by
    rw [← hW, show 64 * (w + 1) = 64 * (w - 1) + 64 + 64 by omega_using [hw], Nat.pow_add, Nat.pow_add]
  generalize 2 ^ (64 * (w - 1)) = B at *
  have hM0 : 0 < M := by omega_using [hXM]
  -- `x 2^64 = (u₂ 2^64 + u₁) B + xₗ 2^64`, with `xₗ 2^64 < B`.
  have hY : X * 2 ^ 64 = (u2 * 2 ^ 64 + u1) * B + Xl * 2 ^ 64 := by rw [hX, hB]; grind
  have hYl : Xl * 2 ^ 64 < B := by rw [hB]; exact Nat.mul_lt_mul_of_pos_right hXl (Nat.two_pow_pos 64)
  -- `q < 2^64`.
  have hq : X * 2 ^ 64 / M < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul hM0, Nat.mul_comm (2 ^ 64) M]; exact Nat.mul_lt_mul_of_pos_right hXM (Nat.two_pow_pos 64)
  rw [hY, hM] at hq
  have hge := qhat_ge hYl (by omega_using [hd]) hq
  have hle := qhat_le hml hd hq
  rw [← hY, ← hM] at hge hle
  generalize min ((u2 * 2 ^ 64 + u1) / d) (2 ^ 64 - 1) = qh at *
  -- `4 m < W / 2`.
  have hMW : 4 * M < W / 2 := by
    have : M < B * 2 ^ 64 := by
      have := Nat.mul_le_mul_right B (show d + 1 ≤ 2 ^ 64 by omega_using [hd'])
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ 64)] at this
      rw [hM]; omega_using [hml, this]
    rw [hWB]; omega_using [this]
  obtain ⟨hfin, hv1, hv2, hw1, hw2⟩ := addBack_two (W := W) hM0 hMW hge hle
  have e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  have e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc1 h2
  have hv1' : -((W : Int) / 2) ≤ addIfNeg M (addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat))) := by
    rw [hfin]; omega_using []
  have hv2' : addIfNeg M (addIfNeg M ((X * 2 ^ 64 : Nat) - (qh * M : Nat))) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt (X * 2 ^ 64) hM0; omega_using [hMW, this]
  have e3 := twos_of_add hw1 hw2 hv1' hv2' e2 hT3 hc2 h3
  rw [e3, hfin]
  have hr := Nat.mod_lt (X * 2 ^ 64) hM0
  have hMW' : M < W := Nat.lt_of_lt_of_le (by omega_using [hMW]) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

end VG.Proof.Bignum.WordStep
