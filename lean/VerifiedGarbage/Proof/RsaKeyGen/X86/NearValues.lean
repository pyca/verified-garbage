module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearTop
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-! # Relate the threshold comparison's bitwise accumulators to native integers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.Proof.Mont

theorem word_zero (x : BitVec 32) : x = 0#32 ↔ x.toNat = 0 :=
  ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩

theorem high_zero (m : Mem) (base : Addr) (out : Nat) :
    (word m base out ||| word m base (out + 4)) ||| word m base (out + 8) = 0#32 ↔
      val32 m base out 3 = 0 := by
  simp only [BitVec.or_eq_zero_iff, word_zero]
  change ((w32 m base out = 0 ∧ w32 m base (out + 4) = 0) ∧ w32 m base (out + 8) = 0) ↔ _
  simp [val32, Nat.add_assoc, and_assoc, Nat.mul_eq_zero]

theorem low_mask (x : BitVec 32) : (x &&& 0x0fffffff).toNat = x.toNat % 2 ^ 28 := by
  rw [BitVec.toNat_and]
  change x.toNat &&& (2 ^ 28 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod ..

theorem low_zero (acc x : BitVec 32) :
    (acc ||| (x &&& 0x0fffffff)).toNat = 0 ↔ acc = 0#32 ∧ x.toNat % 2 ^ 28 = 0 := by
  rw [← word_zero, BitVec.or_eq_zero_iff, word_zero (x &&& 0x0fffffff), low_mask]

theorem nibble_value (x : BitVec 32) : (x >>> 28).toNat = x.toNat / 2 ^ 28 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem nibble_bound (x : BitVec 32) : (x >>> 28).toNat < 16 := by
  rw [nibble_value]
  have := x.isLt
  omega

end VG.Proof.RsaKeyGen.X86.Near
