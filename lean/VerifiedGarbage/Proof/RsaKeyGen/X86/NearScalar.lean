module

import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.Omega

/-! # Scalar flags used by the RSA separation comparison -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near

def bit (b : Bool) : BitVec 32 := BitVec.ofNat 32 b.toNat

theorem bit_toNat (b : Bool) : (bit b).toNat = b.toNat := by cases b <;> rfl

theorem carry_bit (b : Bool) : (BitVec.ofBool b).setWidth 32 = bit b := by cases b <;> rfl

theorem bit_and (a b : Bool) : bit a &&& bit b = bit (a && b) := by cases a <;> cases b <;> rfl

theorem nonzero_bit (low : BitVec 32) :
    1#32 - 0#32 - (BitVec.ofBool (decide (low.toNat < 1))).setWidth 32 = bit (decide (low.toNat ≠ 0)) := by
  by_cases zero : low.toNat = 0
  · rw [zero, decide_eq_true (by decide : (0 : Nat) < 1), decide_eq_false (by decide : ¬ (0 : Nat) ≠ 0)]
    rfl
  · rw [decide_eq_false (by omega : ¬ low.toNat < 1), decide_eq_true zero]
    rfl

theorem nibble_sum (nibble low : BitVec 32) (bound : nibble.toNat < 16) :
    (nibble + bit (decide (low.toNat ≠ 0))).toNat = nibble.toNat + (decide (low.toNat ≠ 0)).toNat := by
  rw [BitVec.toNat_add, bit_toNat]
  have delta : (decide (low.toNat ≠ 0)).toNat ≤ 1 := by cases decide (low.toNat ≠ 0) <;> decide
  omega

end VG.Proof.RsaKeyGen.X86.Near
