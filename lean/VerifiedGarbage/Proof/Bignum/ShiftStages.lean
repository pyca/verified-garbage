module

import VerifiedGarbage.Proof.Framework.Omega

-- separate module: target-independent, for every architecture's shifts by stages

/-!
# Shifts by stages

A count `T` below `2^(K + 1)`, taken by stages of `2^K, 2^(K - 1), …, 1`
from the largest down, each taken where it still fits (`greedy`), is taken
whole (`greedy_pows`): after the stages above `s`, what is left is below
`2 s`. Code tests a stage without knowing `T`, by what `T` counts:

* the trailing zeros `tz y` of `y ≠ 0`, where a stage of `s` is taken if the
  low `s` bits of what is left of `y` are zero (`dvd_iff`): `RecoverDet`'s
  twos of `u ∨ x₂` (the trailing zeros of `gcd(u, x₂)`) and of `u`;
* the leading zeros `63 - log₂ w` of a word `w ≠ 0`, where a stage of `b` is
  taken if `w` shifted so far is below `2^(64 - b)` (`lt_pow_iff`);
* and a count's binary digits from the lowest, for shifts by stages that a
  count's bits choose (`mod_two_pow_succ`).

For two numbers at once, `u / 2^a` and `x / 2^a` both have their low `s` bits
zero exactly when `a + s ≤ tz (gcd u x)` (`stage_pair`).
-/

@[expose] public section

namespace VG.Proof.Bignum.ShiftStages

/-! ## The stages -/

/-- The stages `2^K, …, 2, 1`. -/
def pows : Nat → List Nat
  | 0 => [1]
  | K + 1 => 2 ^ (K + 1) :: pows K

/-- `acc` and the stages of `ss` that fit below `T`, taken from the first. -/
def greedy (T : Nat) (ss : List Nat) (acc : Nat) : Nat :=
  ss.foldl (fun a s => if a + s ≤ T then a + s else a) acc

theorem greedy_cons (T s : Nat) (ss : List Nat) (acc : Nat) :
    greedy T (s :: ss) acc = greedy T ss (if acc + s ≤ T then acc + s else acc) := rfl

theorem greedy_nil (T acc : Nat) : greedy T [] acc = acc := rfl

/-- The stages from `2^K` take a count `T` below `2^(K + 1)` whole. -/
theorem greedy_pows : ∀ (K T acc : Nat), acc ≤ T → T - acc < 2 ^ (K + 1) → greedy T (pows K) acc = T
  | 0, T, acc, h1, h2 => by
    simp only [pows, greedy_cons, greedy_nil]
    split <;> omega_arith
  | K + 1, T, acc, h1, h2 => by
    simp only [pows, greedy_cons]
    have hp : 2 ^ (K + 1 + 1) = 2 * 2 ^ (K + 1) := by rw [Nat.pow_succ]; omega_using []
    split
    · exact greedy_pows K T _ (by omega_arith) (by omega_using [h2])
    · exact greedy_pows K T _ h1 (by omega_arith)

/-! ## Trailing zeros -/

/-- The trailing zeros of `n` (`0` for `0`). -/
def tz (n : Nat) : Nat := if h : n = 0 ∨ n % 2 = 1 then 0 else tz (n / 2) + 1
termination_by n
decreasing_by omega_using [h]

theorem tz_spec : ∀ (n : Nat), n ≠ 0 → 2 ^ tz n ∣ n ∧ n / 2 ^ tz n % 2 = 1
  | n, h0 => by
    unfold tz
    split
    · rename_i h
      simp only [Nat.pow_zero, Nat.one_dvd, Nat.div_one, true_and]; omega_using [h0, h]
    · rename_i h
      have h2 : n % 2 = 0 := by omega_using [h]
      obtain ⟨d, hd⟩ := tz_spec (n / 2) (by omega_using [h])
      refine ⟨?_, ?_⟩
      · obtain ⟨c, hc⟩ := d
        exact ⟨c, by rw [Nat.pow_succ, Nat.mul_right_comm, ← hc]; omega_using [h]⟩
      · rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]; exact hd
termination_by n => n
decreasing_by omega_using [h0]

/-- `2^s` divides `n ≠ 0` exactly for `s` up to its trailing zeros. -/
theorem dvd_iff {n : Nat} (h0 : n ≠ 0) (s : Nat) : 2 ^ s ∣ n ↔ s ≤ tz n := by
  obtain ⟨d, o⟩ := tz_spec n h0
  generalize tz n = t at d o ⊢
  constructor
  · intro hs
    by_cases hle : s ≤ t
    · exact hle
    · exfalso
      have h1 : 2 ^ (t + 1) ∣ n := Nat.pow_dvd_of_le_of_pow_dvd (by omega_using [hle]) hs
      obtain ⟨c, hc⟩ := h1
      have : n / 2 ^ t = 2 * c := by
        rw [hc, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
      omega_using [o, this]
  · intro hs
    exact Nat.pow_dvd_of_le_of_pow_dvd hs d

/-- The trailing zeros of `0 < N < 2^k` are below `k`. -/
theorem tz_lt {N k : Nat} (pos : 0 < N) (hk : N < 2 ^ k) : tz N < k := by
  have := (dvd_iff (show N ≠ 0 by omega_using [pos]) (tz N)).mpr (Nat.le_refl _)
  have := Nat.le_of_dvd pos this
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt this hk)

/-- After shifting by `a` of its trailing zeros, `n` has `tz n - a` left. -/
theorem tz_div {n : Nat} (h0 : n ≠ 0) {a : Nat} (ha : a ≤ tz n) : tz (n / 2 ^ a) = tz n - a := by
  have hd : 2 ^ a ∣ n := (dvd_iff h0 a).mpr ha
  obtain ⟨c, hc⟩ := hd
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact h0 hc
  have e : n / 2 ^ a = c := by rw [hc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  rw [e]
  apply Nat.le_antisymm
  · have : 2 ^ (a + tz c) ∣ n := by
      rw [hc, Nat.pow_add]; exact Nat.mul_dvd_mul_left _ ((dvd_iff hc0 _).mpr (Nat.le_refl _))
    have := (dvd_iff h0 _).mp this
    omega_using [this]
  · have : 2 ^ (tz n - a) ∣ c := by
      have h1 : 2 ^ a * 2 ^ (tz n - a) ∣ 2 ^ a * c := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' ha, ← hc]; exact (dvd_iff h0 _).mpr (Nat.le_refl _)
      exact Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos _) h1
    exact (dvd_iff hc0 _).mp this

/-- A stage of the trailing zeros: with `a` of them taken, the low `s` bits of
`n / 2^a` are zero exactly when `a + s` fits. -/
theorem stage_tz {n : Nat} (h0 : n ≠ 0) {a : Nat} (ha : a ≤ tz n) (s : Nat) :
    n / 2 ^ a % 2 ^ s = 0 ↔ a + s ≤ tz n := by
  have hc0 : n / 2 ^ a ≠ 0 := by
    intro h
    have : 2 ^ a ∣ n := (dvd_iff h0 a).mpr ha
    obtain ⟨c, hc⟩ := this
    rw [hc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)] at h
    subst h; simp at hc; exact h0 hc
  rw [← Nat.dvd_iff_mod_eq_zero, dvd_iff hc0, tz_div h0 ha]
  omega_using [ha]

/-- Two numbers' common factors of two are their GCD's. -/
theorem dvd_gcd_iff {u x : Nat} (s : Nat) : 2 ^ s ∣ u ∧ 2 ^ s ∣ x ↔ 2 ^ s ∣ Nat.gcd u x :=
  ⟨fun ⟨h1, h2⟩ => Nat.dvd_gcd h1 h2, fun h => ⟨Nat.dvd_trans h (Nat.gcd_dvd_left u x),
    Nat.dvd_trans h (Nat.gcd_dvd_right u x)⟩⟩

/-! ## Leading zeros -/

/-- `w 2^a < 2^m` for `w ≠ 0` exactly when `log₂ w + a < m`. -/
theorem lt_pow_iff {w : Nat} (h0 : w ≠ 0) (a m : Nat) : w * 2 ^ a < 2 ^ m ↔ Nat.log2 w + a < m := by
  have lo : 2 ^ Nat.log2 w ≤ w := Nat.log2_self_le h0
  have hi : w < 2 ^ (Nat.log2 w + 1) := Nat.lt_log2_self
  constructor
  · intro h
    have : 2 ^ (Nat.log2 w + a) < 2 ^ m := by
      rw [Nat.pow_add]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ lo) h
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  · intro h
    calc w * 2 ^ a < 2 ^ (Nat.log2 w + 1) * 2 ^ a := Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos _)
      _ = 2 ^ (Nat.log2 w + 1 + a) := by rw [← Nat.pow_add]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega_using [h])

/-- A stage of the leading zeros of a word `w ≠ 0`: with `a` of them taken,
`w 2^a` is below `2^(64 - b)` exactly when `a + b` fits in `63 - log₂ w`. -/
theorem stage_clz {w : Nat} (h0 : w ≠ 0) (a b : Nat) (hb : b ≤ 64) :
    w * 2 ^ a < 2 ^ (64 - b) ↔ a + b ≤ 63 - Nat.log2 w ∧ Nat.log2 w < 64 := by
  rw [lt_pow_iff h0]; omega

/-! ## A count's bits -/

/-- The low `j + 1` bits of `c`: its low `j` and bit `j`. -/
theorem mod_two_pow_succ (c j : Nat) : c % 2 ^ (j + 1) = c % 2 ^ j + c / 2 ^ j % 2 * 2 ^ j := by
  rw [Nat.pow_succ, Nat.mod_mul, Nat.add_comm, Nat.mul_comm (c / 2 ^ j % 2)]
  exact Nat.add_comm _ _

/-! ## Two numbers' common twos -/

/-- With `2^a ∣ n`, the low `s` bits of `n / 2^a` are zero exactly when `2^(a + s) ∣ n`. -/
theorem div_mod_pow_iff {n a : Nat} (h : 2 ^ a ∣ n) (s : Nat) : n / 2 ^ a % 2 ^ s = 0 ↔ 2 ^ (a + s) ∣ n := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), ← Nat.dvd_iff_mod_eq_zero, Nat.pow_add]
  exact (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos _)).symm

/-- A stage of two numbers' common trailing zeros `tz (gcd u x)`: with `a` of
them taken, the low `s` bits of both `u / 2^a` and `x / 2^a` are zero exactly
when `a + s` fits. -/
theorem stage_pair {u x : Nat} (hu : u ≠ 0) {a : Nat} (ha : a ≤ tz (Nat.gcd u x)) (s : Nat) :
    (u / 2 ^ a % 2 ^ s = 0 ∧ x / 2 ^ a % 2 ^ s = 0) ↔ a + s ≤ tz (Nat.gcd u x) := by
  have hg : Nat.gcd u x ≠ 0 := Nat.gcd_ne_zero_left hu
  have hd : 2 ^ a ∣ Nat.gcd u x := (dvd_iff hg a).mpr ha
  rw [div_mod_pow_iff (Nat.dvd_trans hd (Nat.gcd_dvd_left u x)),
    div_mod_pow_iff (Nat.dvd_trans hd (Nat.gcd_dvd_right u x)), dvd_gcd_iff, dvd_iff hg]

/-- The stages compose: shifts right by `a` then `s` bits, and left modulo `2^b`. -/
theorem div_pow_add (n a s : Nat) : n / 2 ^ a / 2 ^ s = n / 2 ^ (a + s) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem mul_pow_add_mod (x a s b : Nat) : x * 2 ^ a % 2 ^ b * 2 ^ s % 2 ^ b = x * 2 ^ (a + s) % 2 ^ b := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc, ← Nat.pow_add]

end VG.Proof.Bignum.ShiftStages
