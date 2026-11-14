module

public import VerifiedGarbage.Proof.Ed25519.Word64

/-! Carry extraction shared by the fused point kernels. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64

theorem point_self_sub (x : Word) : x + ~~~x + BitVec.ofNat 64 true.toNat = 0 := by
  change x + ~~~x + (1#64) = 0#64
  rw [BitVec.add_assoc,←BitVec.neg_eq_not_add,BitVec.add_right_neg]

theorem point_zero_word : (BitVec.setWidth 64 (0 : BitVec 16) <<< 0)=(0 : Word) := rfl

theorem addCarry_zero (c : Bool) : addCarry 0 0 c=BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

end VG.Proof.Mont.AArch64.P521Field
