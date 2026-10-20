module

public import VerifiedGarbage.Proof.Framework.PowLit

/-! # Montgomery reduction with packed 32-bit words

The RSA workspace retains its existing 64-bit-word layout. ARMv7 scans
its words in pairs of 32-bit limbs, with radix `2^32` at each round.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm

/-- The sum of a round: below `2³³ m`, if `T < 2m`, `a < 2³²`, `b < m` and
`u < 2³²`. -/
theorem round_sum_lt {T a b u m : Nat} (hT : T < 2 * m) (ha : a < 2 ^ 32) (hb : b < m)
    (hu : u < 2 ^ 32) : T + a * b + u * m < 2 ^ 33 * m := by
  have h1 : a * b ≤ (2 ^ 32 - 1) * b := Nat.mul_le_mul_right _ (by omega)
  have h2 : u * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  have h3 : (2 ^ 32 - 1) * b ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.sub_mul, Nat.one_mul] at h1 h2 h3
  have : 2 ^ 33 * m = 2 * 2 ^ 32 * m := by rw [show (2 : Nat) ^ 33 = 2 * 2 ^ 32 by decide]
  omega

/-- A round keeps the accumulator below `2m`. -/
theorem round_lt {T T' a b u m : Nat} (h : 2 ^ 32 * T' = T + a * b + u * m) (hT : T < 2 * m)
    (ha : a < 2 ^ 32) (hb : b < m) (hu : u < 2 ^ 32) : T' < 2 * m := by
  have := round_sum_lt hT ha hb hu
  rw [← h, show 2 ^ 33 * m = 2 ^ 32 * (2 * m) by
    rw [show (2 : Nat) ^ 33 = 2 ^ 32 * 2 by decide, Nat.mul_assoc]] at this
  exact Nat.lt_of_mul_lt_mul_left this

/-- The accumulator after a round, times `2³²`, modulo `m`. -/
theorem round_mod {T T' a b u m : Nat} (h : 2 ^ 32 * T' = T + a * b + u * m) :
    2 ^ 32 * T' % m = (T + a * b) % m := by
  rw [h, Nat.add_mul_mod_self_right]

/-- The rounds' invariant `2^(32 i) T ≡ A_i B (mod m)`, one round on. -/
theorem round_step {P T T' a b u m A : Nat} (h : 2 ^ 32 * T' = T + a * b + u * m)
    (hI : P * T % m = A * b % m) : P * 2 ^ 32 * T' % m = (A + P * a) * b % m := by
  have e : P * 2 ^ 32 * T' = P * T + P * a * b + P * u * m := by
    rw [Nat.mul_assoc, h, Nat.mul_add, Nat.mul_add, Nat.mul_assoc P a, Nat.mul_assoc P u]
  rw [e, Nat.add_mul_mod_self_right, Nat.add_mod, hI, ← Nat.add_mod, Nat.add_mul]


/-- `t₀ + (t₀ m' mod 2³²) m ≡ 0 (mod 2³²)` when `m m' ≡ -1`. -/
theorem mont_low (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 32 = 0) :
    (t0 * minv % 2 ^ 32 * m + t0) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 32), Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    show t0 * minv * m + t0 = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m],
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]


/-- The existing 64-bit Montgomery inverse supplies its low 32 bits
without a second precomputation or a change to the RSA workspace. -/
theorem inverse32 {m inv : Nat} (h : (m * inv + 1) % 2 ^ 64 = 0) :
    (m * (inv % 2 ^ 32) + 1) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    ← Nat.mod_mod_of_dvd (m * inv + 1) (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩), h]

/-- Two 32-bit rounds per workspace word retain the existing Montgomery radix. -/
theorem radix32 (w : Nat) : (2 : Nat) ^ (32 * (2 * w)) = 2 ^ (64 * w) := by
  congr 1
  omega

/-- What `subMod` and `selectAcc` leave: for `T = T_l + R (T_w + 2³² T_{w+1}) < 2m`
(`T_l < R` its low words, `m < R`) and `D + m = T_l + R c` (`D < R`, `c` the
borrow), `T_l` if `T_w < c` and `D` otherwise is `T mod m`. -/
theorem csub_result {Tl Tw Tw1 D m R c : Nat} (hm : m < R) (hD : D < R) (hc : c ≤ 1)
    (hTl : Tl < R) (hT : Tl + R * (Tw + 2 ^ 32 * Tw1) < 2 * m) (hsub : D + m = Tl + R * c) :
    (if Tw < c then Tl else D) = (Tl + R * (Tw + 2 ^ 32 * Tw1)) % m := by
  have hR : 0 < R := by omega
  -- The top words: `T_{w+1} = 0` and `T_w ≤ 1`.
  have h1 : Tw1 = 0 := by
    rcases Nat.eq_zero_or_pos Tw1 with h | h
    · exact h
    · have : R * 2 ^ 32 ≤ R * (Tw + 2 ^ 32 * Tw1) := Nat.mul_le_mul_left _ (by
        have := Nat.mul_le_mul_left (2 ^ 32) h; omega)
      have : R * 2 ^ 32 ≥ 2 * R := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by decide)
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
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · have : c = 1 := by omega
      subst this
      simp only [Nat.zero_lt_one, ite_true]
      rw [Nat.mod_eq_of_lt (by omega)]
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
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

end VG.Proof.Bignum.Arm
