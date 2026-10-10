import VerifiedGarbage.Spec.Ctr

/-!
# CTR: counter blocks as big-endian numbers

Untrusted: everything here is checked by Lean, from `Spec/Ctr.lean` alone.
Big-endian numbers in bytes (`toNat`, `ofNat`), the counter blocks
(`next`, `counters`), and the counter block after `k` increments as
`t + k` (`next_eq`). Light on imports, for every mode built on CTR's
counter (`Ctr32.lean`, SM4-CTR).
-/

namespace VG.Proof.AesCtr

open VG Spec.Ctr

/-! ## Big-endian numbers in bytes -/

theorem length_ofNat (x k : Nat) : (ofNat x k).length = k := by simp [ofNat]

theorem toNat_append (a b : List Byte) : toNat (a ++ b) = toNat a * 256 ^ b.length + toNat b := by
  suffices ∀ acc, (b.foldl (fun a b => 256 * a + b.toNat) acc) =
      acc * 256 ^ b.length + b.foldl (fun a b => 256 * a + b.toNat) 0 by
    simp only [toNat, List.foldl_append]; exact this _
  induction b with
  | nil => simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons, Nat.mul_zero, Nat.zero_add]
    rw [ih, ih (x.toNat), Nat.pow_succ]
    grind

theorem ofNat_succ (x k : Nat) : ofNat x (k + 1) = ofNat (x / 256) k ++ [BitVec.ofNat 8 x] := by
  apply List.ext_getElem (by simp [length_ofNat])
  intro i h₁ _
  simp only [length_ofNat] at h₁
  simp only [ofNat, List.getElem_map, List.getElem_range]
  by_cases hi : i < k
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range, Nat.div_div_eq_div_mul]
    congr 2
    rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  · rw [List.getElem_append_right (by simp; omega)]
    simp [show i = k by omega]

/-- `ofNat x k` is the `k`-byte representation of `x mod 256ᵏ`. -/
theorem toNat_ofNat (x k : Nat) : toNat (ofNat x k) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [ofNat, toNat, Nat.mod_one]
  | succ k ih =>
    rw [ofNat_succ, toNat_append, ih]
    simp only [List.length_singleton, Nat.pow_one, toNat, List.foldl_cons, List.foldl_nil, Nat.mul_zero,
      Nat.zero_add, BitVec.toNat_ofNat]
    have e : x % 256 ^ (k + 1) = x % 256 + 256 * (x / 256 % 256 ^ k) := by rw [Nat.pow_succ', Nat.mod_mul]
    rw [e]
    omega

theorem ofNat_add (x k j : Nat) : ofNat x (k + j) = ofNat (x / 256 ^ j) k ++ ofNat x j := by
  induction j generalizing x with
  | zero => simp [ofNat]
  | succ j ih =>
    rw [← Nat.add_assoc, ofNat_succ, ih, ofNat_succ, List.append_assoc, Nat.div_div_eq_div_mul,
      ← Nat.pow_succ']

theorem ofNat_congr {x y k : Nat} (h : x % 256 ^ k = y % 256 ^ k) : ofNat x k = ofNat y k := by
  apply List.ext_getElem (by simp [length_ofNat])
  intro i h₁ _
  simp only [length_ofNat] at h₁
  simp only [ofNat, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hd : 256 ^ (k - 1 - i) * 256 ∣ 256 ^ k := by
    rw [← Nat.pow_succ]; exact Nat.pow_dvd_pow 256 (by omega)
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self y, ← Nat.mod_mod_of_dvd x hd,
    ← Nat.mod_mod_of_dvd y hd, h]

/-- Adding `x` to the number in `a ++ b`: the sum's last `|b|` bytes are
those of `b + x`, and its first `|a|` those of `a` plus the carry. -/
theorem ofNat_toNat_append_add (a b : List Byte) (x : Nat) :
    ofNat (toNat (a ++ b) + x) (a.length + b.length) =
      ofNat (toNat a + (toNat b + x) / 256 ^ b.length) a.length ++ ofNat (toNat b + x) b.length := by
  rw [ofNat_add, toNat_append]
  have hp : 0 < 256 ^ b.length := Nat.pow_pos (by decide)
  congr 1
  · congr 1
    rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.add_comm]
  · apply ofNat_congr
    rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]

/-! ## Counter blocks -/

theorem length_counters (t : List Byte) (n : Nat) : (counters t n).length = n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [counters, ih]

theorem next_succ (t : List Byte) (n : Nat) : next t (n + 1) = inc (next t n) := rfl

theorem next_succ' (t : List Byte) (n : Nat) : next t (n + 1) = next (inc t) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [next_succ, ih, ← next_succ]

theorem counters_succ (t : List Byte) (n : Nat) : counters t (n + 1) = counters t n ++ [next t n] := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => rw [counters, ih, counters, next_succ']; rfl

theorem toNat_lt_pow : ∀ t : List Byte, toNat t < 256 ^ t.length
  | [] => by decide
  | b :: u => by
    have hb : b.toNat + 1 ≤ 256 := b.isLt
    have hu := toNat_lt_pow u
    rw [show b :: u = [b] ++ u from rfl, toNat_append, List.length_append, List.length_singleton,
      Nat.pow_add, Nat.pow_one, show toNat [b] = b.toNat by simp [toNat]]
    calc b.toNat * 256 ^ u.length + toNat u < b.toNat * 256 ^ u.length + 256 ^ u.length :=
          Nat.add_lt_add_left hu _
      _ = (b.toNat + 1) * 256 ^ u.length := (Nat.succ_mul _ _).symm
      _ ≤ 256 * 256 ^ u.length := Nat.mul_le_mul_right _ hb

theorem ofNat_toNat_length : ∀ t : List Byte, ofNat (toNat t) t.length = t
  | [] => rfl
  | b :: u => by
    have hb := b.isLt
    have hu := toNat_lt_pow u
    have hp : 0 < 256 ^ u.length := Nat.pow_pos (by decide)
    rw [show b :: u = [b] ++ u from rfl, toNat_append, List.length_append, List.length_singleton,
      ofNat_add]
    simp only [toNat, List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
    simp only [toNat] at hu
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hu, Nat.zero_add]
    congr 1
    · simp only [ofNat, List.range_one, List.map_cons, List.map_nil, Nat.sub_self, Nat.pow_zero,
        Nat.div_one, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [ofNat_congr (y := toNat u) (by rw [Nat.add_mul_mod_self_right]; rfl)]
      exact ofNat_toNat_length u

theorem ofNat_toNat {t : List Byte} (ht : t.length = 16) : ofNat (toNat t) 16 = t := by
  rw [← ht]; exact ofNat_toNat_length t

/-- The counter block after `k` increments: `t + k`, modulo `2¹²⁸`. -/
theorem next_eq {t : List Byte} (ht : t.length = 16) : ∀ k, next t k = ofNat (toNat t + k) 16
  | 0 => (ofNat_toNat ht).symm
  | k + 1 => by
    rw [next_succ, next_eq ht k, inc, toNat_ofNat]
    exact ofNat_congr (by rw [Nat.mod_add_mod, Nat.add_assoc])

theorem counters_add (t : List Byte) : ∀ a b, counters t (a + b) = counters t a ++ counters (next t a) b
  | 0, b => by simp only [Nat.zero_add, counters, List.nil_append]; rfl
  | a + 1, b => by
    rw [Nat.add_right_comm, counters, counters_add (inc t) a b, counters, next_succ']
    rfl

theorem counters_eq_map (t : List Byte) : ∀ n, counters t n = (List.range n).map (next t)
  | 0 => rfl
  | n + 1 => by rw [counters_succ, counters_eq_map t n, List.range_succ, List.map_append]; rfl

end VG.Proof.AesCtr
