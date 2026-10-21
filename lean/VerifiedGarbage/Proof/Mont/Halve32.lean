module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # Native halving between possibly distinct array offsets -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem val32_congr_at (m m' : Mem) (base : Addr) : ∀ (n src out : Nat),
    (∀ i < n, w32 m' base (out + 4 * i) = w32 m base (src + 4 * i)) →
    val32 m' base out n = val32 m base src n
  | 0, _, _, _ => rfl
  | n + 1, src, out, h => by
    rw [val32, val32, show w32 m' base out = w32 m base src by
      simpa only [Nat.mul_zero, Nat.add_zero] using h 0 (by omega)]
    apply congrArg (fun x => w32 m base src + 2 ^ 32 * x)
    apply val32_congr_at m m' base n (src + 4) (out + 4)
    intro i hi
    have e := h (i + 1) (by omega)
    rw [show out + 4 * (i + 1) = out + 4 + 4 * i by omega,
      show src + 4 * (i + 1) = src + 4 + 4 * i by omega] at e
    exact e

theorem val32_parity_at (m : Mem) (base : Addr) (src k : Nat) :
    val32 m base src (k + 1) % 2 = w32 m base src % 2 := by
  rw [val32]
  omega

theorem val32_halve_at (m m' : Mem) (base : Addr) : ∀ (k src out : Nat),
    (∀ i < k, w32 m' base (out + 4 * i) = w32 m base (src + 4 * i) / 2 +
      2 ^ 31 * (if i + 1 = k then 0 else w32 m base (src + 4 * (i + 1)) % 2)) →
    val32 m' base out k = val32 m base src k / 2
  | 0, _, _, _ => by simp only [val32, Nat.zero_div]
  | k + 1, src, out, h => by
    have ih := val32_halve_at m m' base k (src + 4) (out + 4) fun i hi => by
      have e := h (i + 1) (by omega)
      rw [show out + 4 * (i + 1) = out + 4 + 4 * i by omega,
        show src + 4 * (i + 1) = src + 4 + 4 * i by omega,
        show src + 4 * (i + 1 + 1) = src + 4 + 4 * (i + 1) by omega] at e
      rw [e]
      simp only [Nat.add_right_cancel_iff]
    have e := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one] at e
    rw [val32, val32, e, ih]
    cases k with
    | zero =>
      rw [ite_eq_left rfl]
      simp only [val32]
      omega
    | succ k =>
      rw [ite_eq_right (by omega), ← val32_parity_at m base (src + 4) k]
      omega

end VG.Proof.Mont
