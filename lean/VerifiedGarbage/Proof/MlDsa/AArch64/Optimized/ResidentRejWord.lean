import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackWord

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- A masked 23-bit candidate makes the high bit of its difference from q
an exact acceptance bit. No modular wraparound is mistaken for acceptance. -/
theorem candidate_bit (z : BitVec 32) (hz : z.toNat < 2^23) :
    (z - 8380417) >>> 31 = if z.toNat < 8380417 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_sub]
  have hq : (8380417 : BitVec 32).toNat = 8380417 := rfl
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  by_cases h : z.toNat < 8380417
  · rw [ite_eq_left h]
    simp only [hq, h1, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hz ⊢
    omega
  · rw [ite_eq_right h]
    simp only [hq, h0, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hz ⊢
    omega

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
