module

/-! # One doubling of a residue: the sum where it is below the modulus, else the difference -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt

/-- `S = L + B carry = 2 T`, and `D + M = L + B c1` (`D`, `c1` the
difference and borrow of `L − M`): selecting `L` when `carry < c1`, else
`D`, gives `2 T mod M`. -/
theorem double_mod {B M T L D : Nat} {carry c1 : Nat} (hM : M < B) (hT : T < M) (carry1 : carry ≤ 1)
    (c11 : c1 ≤ 1) (hD : D < B) (sum : L + B * carry = T + T) (diff : D + M = L + B * c1) :
    (if carry < c1 then L else D) = (T + T) % M := by
  have hc : carry = 0 ∨ carry = 1 := by omega
  have hb : c1 = 0 ∨ c1 = 1 := by omega
  by_cases hS : T + T < M
  · rw [Nat.mod_eq_of_lt hS]
    rcases hc with rfl | rfl <;> rcases hb with rfl | rfl <;> simp <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rcases hc with rfl | rfl <;> rcases hb with rfl | rfl <;> simp <;> omega

end VG.Proof.RsaKeyGen.X86.PrepareRt
