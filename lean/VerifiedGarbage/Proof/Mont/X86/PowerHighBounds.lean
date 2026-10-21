module

import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Mont.Words

/-! A public high-bit test certifies that the setup seed is reduced. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.Proof.Mont

theorem high_word_bound {mem : Mem} {base : Addr} {out n : Nat}
    (hn : 0 < n) (high : 2^31 ≤ w32 mem base (out+4*(2*n-1))) :
    2^(64*n-1) ≤ wordsVal mem base out n := by
  have width : 2*n = (2*n-1)+1 := by omega
  have exponent : 2^(64*n-1) = 2^(32*(2*n-1)) * 2^31 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [wordsVal_eq_val32, width, val32_succ, exponent]
  have := Nat.mul_le_mul_left (2^(32*(2*n-1))) high
  omega

theorem high_seed_reduced {n m : Nat} (hn : 0 < n)
    (lower : 2^(64*n-1) ≤ m) (odd : m % 2 = 1) : 2^(64*n-1) < m := by
  have power : 64*n-1 = (64*n-2)+1 := by omega
  have even : 2^(64*n-1) % 2 = 0 := by
    rw [power, Nat.pow_succ, Nat.mul_mod]
    simp
  omega

theorem high_seed_doubled {n : Nat} (hn : 0 < n) :
    2^((n+1)+(64*n-1)) = 2^(65*n) := by
  congr 1
  omega

end VG.Proof.Mont.X86.Dynamic
