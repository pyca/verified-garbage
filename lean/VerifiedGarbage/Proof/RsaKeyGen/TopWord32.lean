module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-! # The modulus's high native word detects its required top bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.WordBounds32
open VG VG.Proof.Mont

theorem top_div {m : Mem} {B : Addr} {out n : Nat} (positive : 0 < n) :
    val32 m B out n / 2 ^ (32 * n - 1) = w32 m B (out + 4 * (n - 1)) / 2 ^ 31 := by
  have parts := val32_append m B out (n - 1) 1
  rw [show n - 1 + 1 = n by omega] at parts
  change val32 m B out n = val32 m B out (n - 1) + 2 ^ (32 * (n - 1)) * w32 m B (out + 4 * (n - 1)) at parts
  have top : val32 m B out n / 2 ^ (32 * (n - 1)) = w32 m B (out + 4 * (n - 1)) := by
    rw [parts, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add]
  rw [show 32 * n - 1 = 32 * (n - 1) + 31 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul, top]

end VG.Proof.RsaKeyGen.WordBounds32
