module

public import VerifiedGarbage.Proof.Mont.Words32
import Mathlib.Data.Nat.Bitwise

/-! Setting the low bit of a packed operand implements the p-1 bound. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Proof.Mont

theorem orOne (n : Nat) : n ||| 1 = n + (1 - n % 2) := by
  have div : (n ||| 1) / 2 = n / 2 := by
    have := Nat.or_div_two_pow (a := n) (b := 1) (n := 1)
    simpa using this
  have mod : (n ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
  omega

theorem bitvecOrOne (x : BitVec 32) : (x ||| 1).toNat = x.toNat + (1 - x.toNat % 2) := by
  rw [BitVec.toNat_or, show (1 : BitVec 32).toNat = 1 from rfl, orOne]

theorem val32_setLowBit (m : Mem) (B : Addr) (d k : Nat) (hk : 0 < k)
    (fit : d + 4 * k ≤ 2 ^ 64) :
    val32 (m.writeW (off B d) (m.readW (off B d) 32 ||| 1)) B d k =
      val32 m B d k + (1 - val32 m B d k % 2) := by
  have outside := writeW32_outside m B (m.readW (off B d) 32 ||| 1) (d := d) (by omega)
  have tail := outside.val32 (d := d + 4) (k := k - 1) (by right; omega) (by omega)
  have count : k = (k - 1) + 1 := by omega
  conv_lhs => rw [count, val32]
  conv_rhs => rw [count, val32]
  rw [w32_write_self, tail, bitvecOrOne]
  change _ = w32 m B d + 2 ^ 32 * val32 m B (d + 4) (k - 1) +
    (1 - (w32 m B d + 2 ^ 32 * val32 m B (d + 4) (k - 1)) % 2)
  have parity : (w32 m B d + 2 ^ 32 * val32 m B (d + 4) (k - 1)) % 2 = w32 m B d % 2 := by
    simp [Nat.add_mod, Nat.mul_mod]
  rw [parity]
  simp only [w32]
  omega

theorem belowOdd (x p : Nat) (odd : p % 2 = 1) :
    x + (1 - x % 2) < p ↔ x < p - 1 := by omega

end VG.Proof.Ffdh.Arm
