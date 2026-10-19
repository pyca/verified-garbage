module

public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # Combining RSA call success bits -/

@[expose] public section
namespace VG.Proof.Rsa

def successBits (r2 r1 r3 : BitVec 32) : BitVec 32 := r1 &&& r2 &&& r3 &&& 1

theorem successBits_cases (r2 r1 r3 : BitVec 32) : successBits r2 r1 r3 = 0 ∨ successBits r2 r1 r3 = 1 := by
  unfold successBits
  generalize r1 &&& r2 &&& r3 = x
  have h : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with zero | one
  · exact .inl (BitVec.eq_of_toNat_eq (by rw [h, zero]; rfl))
  · exact .inr (BitVec.eq_of_toNat_eq (by rw [h, one]; rfl))

end VG.Proof.Rsa
