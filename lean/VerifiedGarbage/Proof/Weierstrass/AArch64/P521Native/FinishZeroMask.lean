module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowZeroMask
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Omega

/-! The final projective infinity fix uses a mask for Z=0. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.Word64

def finishZeroMaskCode : List Instr :=
  [.movz .x .x5 1 0,.subs .x .x16 .x1 .x5,.sbc .x .x2 .x7 .x7]

theorem finish_zero_mask_ok (s : State) (zero : s.gpr .x7=0#64) :
    WP isa (.block finishZeroMaskCode) s fun t =>
      t.gpr .x2=(if s.gpr .x1=0#64 then BitVec.allOnes 64 else 0#64) ∧
      Keeps [.x5,.x16,.x2] s t := by
  have carryOne (x : Word) : carryOut x (~~~(1#64)) true=decide (x≠0#64) := by
    simp only [carryOut,BitVec.toNat_ofNat,BitVec.toNat_not,Bool.toNat_true]
    have bound := x.isLt
    have eq : x=0#64 ↔ x.toNat=0 := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact BitVec.eq_of_toNat_eq h
    rw [decide_eq_decide]
    simp only [ne_eq,eq]
    omega_arith
  apply WP.of_runBlock
  simp only [finishZeroMaskCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,Nat.reduceMul,BitVec.shiftLeft_zero,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,BitVec.setWidth_eq,
    zero,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  · change addCarry (0#64) (~~~(0#64)) (carryOut (s.gpr .x1) (~~~(1#64)) true)=_
    rw [carryOne]
    by_cases h : s.gpr .x1=0#64 <;> simp only [h,ne_eq,not_true_eq_false,not_false_eq_true,decide_true,decide_false,ite_true,ite_false] <;> rfl
  · reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Weierstrass.AArch64.P521Native
