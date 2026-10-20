module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Save the exact bit count recovered from its byte width and high-byte mask. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm op2_lsl op2_reg dpVal)

theorem combBitsSave_ok (s : State) {base : BitVec 32} {len width h : Nat}
    (locals : Locals base len s) (positive : 0<width)
    (saved : s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 width)
    (count : s.gpr .r1=BitVec.ofNat 32 h) :
    WP isa (.block bitsSave) s fun t =>
      t.gpr .r1=BitVec.ofNat 32 (8*(width-1)+h) ∧
      t.mem=s.mem.writeW (off (State.addr s.sp) 16) (BitVec.ofNat 32 (8*(width-1)+h)) ∧
      Frame [⟨off (State.addr s.sp) 16,4⟩] s.mem t.mem ∧ Rest [.r1,.r6,.r12] s t := by
  unfold bitsSave
  refine wp_loadStack (a := off (State.addr s.sp) 20) (by decide)
    (addr_add (by have := locals.space.nowrap; omega)) (locals.read (by decide)) fun u load => ?_
  refine wp_dp (op2_imm (by decide)) fun v sub => ?_
  refine wp_mov (op2_lsl (by decide)) fun w shift => ?_
  refine wp_dp (op2_reg _ _) fun z add => ?_
  have r6 : v.gpr .r6=BitVec.ofNat 32 (width-1) := by
    rw [sub.gpr,dpVal,load.gpr,saved]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have r6Shift : w.gpr .r6=BitVec.ofNat 32 (8*(width-1)) := by
    rw [shift.gpr,r6,BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (width-1) * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  have r1 : z.gpr .r1=BitVec.ofNat 32 (8*(width-1)+h) := by
    rw [add.gpr,dpVal,shift.other .r1 (by decide),sub.other .r1 (by decide),load.other .r1 (by decide),count,r6Shift]
    rw [← BitVec.ofNat_add,Nat.add_comm]
  have rest : Rest [.r1,.r6,.r12] s z :=
    (load.rest (by simp)).trans ((sub.rest (by simp)).trans ((shift.rest (by simp)).trans (add.rest (by simp))))
  have mem : z.mem=s.mem := add.mem.trans (shift.mem.trans (sub.mem.trans load.mem))
  refine WP.mono (localStore_ok z .r1 (locals.after rest) (by decide : 16+4≤72) (by decide)) ?_
  rintro t ⟨memT,frameT,restT⟩
  rw [rest.sp,mem,r1] at memT
  rw [rest.sp,mem] at frameT
  exact ⟨(restT.gpr .r1 (by simp)).trans r1,memT,frameT,rest.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm
