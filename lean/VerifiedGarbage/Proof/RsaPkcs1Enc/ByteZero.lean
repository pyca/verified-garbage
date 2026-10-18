module

public import VerifiedGarbage.Proof.Framework.Mem

/-! # A zero padding octet contributes one to the branchless rejection flag -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc
open VG

theorem byte_zero32 (b : Byte) :
    (b.setWidth 32 - 1) >>> 31 = BitVec.ofNat 32 (decide (b = 0)).toNat := by
  by_cases zero : b = 0
  · subst b; rfl
  · have positive : 0 < b.toNat := by
      by_contra no
      apply zero
      apply BitVec.eq_of_toNat_eq
      have : b.toNat = 0 := by omega
      exact this
    have bound := b.isLt
    rw [decide_eq_false zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Bool.toNat_false]
    have one : (1 : BitVec 32).toNat = 1 := rfl
    rw [one]
    omega

end VG.Proof.RsaPkcs1Enc
