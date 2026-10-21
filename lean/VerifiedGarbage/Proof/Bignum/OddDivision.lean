module

import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! Odd-integer division shared by RSA and FFDH exponent setup. -/

@[expose] public section
namespace VG.Proof.Bignum

theorem odd_div {c s : Nat} (hc : c % 2 = 1) (hs : 1 ≤ s) : (c - 1) / 2 ^ s = c / 2 ^ s := by
  obtain ⟨q, rfl⟩ : ∃ q, c = 2 * q + 1 := ⟨c / 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ r), ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  omega

end VG.Proof.Bignum
