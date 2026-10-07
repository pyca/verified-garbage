import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Mont.Words32

/-! # Word positions used by the divstep reduction -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.Proof.Mont

theorem low32 (m : Mem) (base : Addr) (d n : Nat) :
    w32 m base d = val32 m base d (n + 1) % 2 ^ 32 := by
  rw [val32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m.readW (off base d) 32).isLt]

theorem high32 (m : Mem) (base : Addr) (d n : Nat) :
    val32 m base (d + 4) n = val32 m base d (n + 1) / 2 ^ 32 := by
  rw [val32, Nat.add_mul_div_left _ _ (by decide),
    Nat.div_eq_of_lt (m.readW (off base d) 32).isLt, Nat.zero_add]

theorem sign32 (m : Mem) (base : Addr) (d n : Nat) :
    (2 ^ 31 ≤ w32 m base (d + 4 * n)) ↔
      2 ^ (32 * n) * 2 ^ 31 ≤ val32 m base d (n + 1) := by
  have E : w32 m base (d + 4 * n) = val32 m base d (n + 1) / 2 ^ (32 * n) := by
    rw [val32_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add]
  rw [E, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.mul_comm (2 ^ 31)]

end VG.Proof.Weierstrass.X86.Inv
