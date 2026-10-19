module

public import VerifiedGarbage.Impl.Bignum.Arm.Select
public import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # The selection mask chooses the exact word without a branch -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem select_value (a b c : BitVec 32) (hc : c.toNat ≤ 1) :
    ((a ^^^ b) &&& (0 - c)) ^^^ a = if c.toNat = 0 then a else b := by
  by_cases hz : c.toNat = 0
  · have e : c = 0 := BitVec.eq_of_toNat_eq hz
    rw [e]
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, ite_true,
      show (0 : BitVec 32) - 0 = 0 from rfl]
    apply BitVec.eq_of_toNat_eq
    simp
  · have e : c = 1 := BitVec.eq_of_toNat_eq (by change c.toNat = 1; omega)
    rw [e]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl, Nat.one_ne_zero, ite_false,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
    rw [BitVec.xor_comm a b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem selectWord_ok (s : State) (hc : (s.gpr .r11).toNat ≤ 1) :
    WP isa (.block selectWord) s fun t =>
      t.gpr .r3 = (if (s.gpr .r11).toNat = 0 then s.gpr .r1 else s.gpr .r2) ∧
      Preserves [.r3, .r4] s t := by
  apply WP.of_runBlock
  simp only [selectWord, runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some,
    show encodable (0 : BitVec 32) = true from rfl, ↓reduceIte,
    gpr_setReg, reduceCtorEq]
  refine ⟨_, rfl, ?_, ?_⟩
  · exact select_value _ _ _ hc
  · repeat first
      | apply Preserves.setReg (hr := by simp)
      | exact Preserves.refl _ _

end VG.Proof.Bignum.Arm
