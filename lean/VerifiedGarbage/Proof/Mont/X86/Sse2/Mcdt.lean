module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Mxcsr
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset

/-! # An MCDT frame

`frame (mcdtEnter r) body mcdtLeave`: the body runs from `mcdtPushed r s`,
inside one more MCDT frame, with MXCSR's saved value at `esp + 4`; if it
keeps that word, its MCDT depth and `esp`, the pop leads to `mcdtPopped`
(`WP.mcdtFrame`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86

/-- The state after an MCDT frame's push. -/
def mcdtPushed (r : Reg) (s : State) : State :=
  { (s.setReg .esp (s.gpr .esp - 12)).setReg r 0x1FBF with
    mem := (s.mem.writeW ((s.gpr .esp - 8).setWidth 64) (mcdtSaved s.mcdt s.mxcsr)).writeW
      ((s.gpr .esp - 12).setWidth 64) (0x1FBF : BitVec 32)
    mcdt := s.mcdt + 1, wr := ⟨(s.gpr .esp - 12).setWidth 64, 9⟩ :: s.wr }

/-- The state after an MCDT frame's pop, from the state `s` its body ends in. -/
def mcdtPopped (s : State) : State :=
  { s.setReg .esp (s.gpr .esp + 12) with mcdt := s.mcdt - 1, wr := s.wr.tail }

theorem mcdtPushed_esp (r : Reg) (s : State) (hr : r ≠ .esp) :
    (mcdtPushed r s).gpr .esp = s.gpr .esp - 12 := by
  simp [mcdtPushed, State.setReg, Ne.symm hr]

theorem mcdtPushed_gpr (r : Reg) (s : State) {q : Reg} (hq : q ≠ .esp) (hqr : q ≠ r) :
    (mcdtPushed r s).gpr q = s.gpr q := by
  simp [mcdtPushed, State.setReg, hq, hqr]

theorem mcdtPushed_mcdt (r : Reg) (s : State) : (mcdtPushed r s).mcdt = s.mcdt + 1 := rfl
theorem mcdtPushed_rd (r : Reg) (s : State) : (mcdtPushed r s).rd = s.rd := rfl
theorem mcdtPushed_wr (r : Reg) (s : State) :
    (mcdtPushed r s).wr = ⟨(s.gpr .esp - 12).setWidth 64, 9⟩ :: s.wr := rfl
theorem mcdtPushed_mxcsr (r : Reg) (s : State) : (mcdtPushed r s).mxcsr = s.mxcsr := rfl

theorem mcdtPopped_esp (s : State) : (mcdtPopped s).gpr .esp = s.gpr .esp + 12 := by
  simp [mcdtPopped, State.setReg]
theorem mcdtPopped_gpr (s : State) {q : Reg} (hq : q ≠ .esp) : (mcdtPopped s).gpr q = s.gpr q := by
  simp [mcdtPopped, State.setReg, hq]
theorem mcdtPopped_mem (s : State) : (mcdtPopped s).mem = s.mem := rfl
theorem mcdtPopped_rd (s : State) : (mcdtPopped s).rd = s.rd := rfl
theorem mcdtPopped_wr (s : State) : (mcdtPopped s).wr = s.wr.tail := rfl
theorem mcdtPopped_mcdt (s : State) : (mcdtPopped s).mcdt = s.mcdt - 1 := rfl

/-- The pushed frame holds MXCSR's value at `esp + 4`. -/
theorem mcdtPushed_saved (r : Reg) (s : State) (hr : r ≠ .esp) (hn : 12 ≤ (s.gpr .esp).toNat) :
    (mcdtPushed r s).mem.readW (((mcdtPushed r s).gpr .esp + 4).setWidth 64) 32 = mcdtSaved s.mcdt s.mxcsr := by
  rw [mcdtPushed_esp r s hr]
  have he : ((s.gpr .esp - 12 + 4).setWidth 64 : Addr) = (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl, show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  have he8 : ((s.gpr .esp - 8).setWidth 64 : Addr) = (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl, show (8 : BitVec 32).toNat = 8 from rfl]
    omega
  simp only [mcdtPushed]
  rw [he, he8, Mem.readW_writeW_sep (fun x h₁ h₂ => by
      rw [Offset.lt_iff x _ (by decide : 4 + 4 ≤ 2 ^ 64)] at h₁
      omega) (by decide),
    Mem.readW_writeW_self32]

theorem mcdt_push {r : Reg} {s : State} (hr : r ≠ .esp) (hn : 12 ≤ (s.gpr .esp).toNat) :
    isa.push (.mcdtEnter r) s = some (mcdtPushed r s) := by
  simp only [isa, push, ne_eq, hr, not_false_eq_true, hn, and_self, ite_true]
  rfl

/-- An MCDT frame whose body keeps `esp`, its depth and the saved MXCSR word. -/
theorem WP.mcdtFrame {r : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hr : r ≠ .esp) (hn : 12 ≤ (s.gpr .esp).toNat) (hsp : NoSp body)
    (hb : WP isa body (mcdtPushed r s) fun s₂ => s₂.mcdt = s.mcdt + 1 ∧
      s₂.mem.readW ((s₂.gpr .esp + 4).setWidth 64) 32 = mcdtSaved s.mcdt s.mxcsr ∧ Q (mcdtPopped s₂)) :
    WP isa (.frame (.mcdtEnter r) body .mcdtLeave) s Q := by
  obtain ⟨t, s₂, he, hm, hs, hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hp := Exec.gpr hsp he
  have hx := Exec.mxcsr he
  have hpop : isa.pop .mcdtLeave (mcdtPushed r s) s₂ = some (mcdtPopped s₂) := by
    simp only [isa, pop]
    refine (ite_eq_left ⟨by omega, hp, hw, ?_, ?_⟩).trans rfl
    · rw [mcdtPushed_wr, mcdtPushed_esp r s hr]; rfl
    · rw [hs, hm, hx, mcdtPushed_mxcsr, Nat.add_sub_cancel]
  exact ⟨_, _, Exec.frame (mcdt_push hr hn) he hpop, hq⟩

end VG.Proof.Mont.X86.Sse2
