module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.RsaKeyGen.Near

/-! # The RSA separation threshold in native little-endian words -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.Mont

theorem near_words32 (m : Mem) (base : Addr) (out n : Nat) (positive : 4 ≤ n) :
    val32 m base out n ≤ 2 ^ (32 * n - 100) ↔
      val32 m base (out + 4 * (n - 4) + 4) 3 = 0 ∧
      w32 m base (out + 4 * (n - 4)) / 2 ^ 28 +
        (decide (val32 m base out (n - 4) ≠ 0 ∨
          w32 m base (out + 4 * (n - 4)) % 2 ^ 28 ≠ 0)).toNat ≤ 1 := by
  have split : val32 m base out n = val32 m base out (n - 4) + 2 ^ (32 * (n - 4)) *
      (w32 m base (out + 4 * (n - 4)) + 2 ^ 32 * val32 m base (out + 4 * (n - 4) + 4) 3) := by
    have H := val32_append m base out (n - 4) 4
    rw [show n - 4 + 4 = n by omega] at H
    exact H
  have power : 2 ^ (32 * n - 100) = 2 ^ (32 * (n - 4)) * 2 ^ 28 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [split, power, le_native_threshold (Nat.two_pow_pos _) (val32_lt ..)]

end VG.Proof.RsaKeyGen
