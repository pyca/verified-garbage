module

public import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Mont.X86.MulRt

/-! # Public flags at the fixed-width square's dispatch points -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont.X86.Rt

 def sizeChoice (K : Nat) : List Instr :=
 [.mov .eax (.mem Impl.Mont.X86.Rt.argN),.alu .cmp .eax (.imm (BitVec.ofNat 32 (K/2)))]
 def aliasChoice : List Instr :=
 [.mov .eax (.mem Impl.Mont.X86.Rt.argA),.mov .edx (.mem Impl.Mont.X86.Rt.argB),.alu .cmp .eax (.reg .edx)]
 def sizeTaint : VG.X86.Taint.T := {regs:=.ofList [.esp,.eax],flags:=true,argLen:=40}
 def aliasTaint : VG.X86.Taint.T := {regs:=.ofList [.esp,.eax,.edx],flags:=true,argLen:=40}

 theorem sizeChoice_check (K : Nat) : VG.Taint.check taint rtTaint (.block (sizeChoice K)) (.block [])=some sizeTaint := by
  rfl
 theorem aliasChoice_check : VG.Taint.check taint rtTaint (.block aliasChoice) (.block [])=some aliasTaint := by
  rfl

 theorem sizeTaint_forget {s t : State} (h : VG.X86.Taint.Agree sizeTaint s t) : VG.X86.Taint.Agree rtTaint s t := by
  exact h.mono (by intro r; cases r <;> decide) (by decide) (by decide) (by decide) (by intro i k hk; simp only [rtTaint,VG.Slots.has_empty,Bool.false_eq_true] at hk) (by decide) (by decide) (by decide) (by decide)
 theorem aliasTaint_forget {s t : State} (h : VG.X86.Taint.Agree aliasTaint s t) : VG.X86.Taint.Agree rtTaint s t := by
  exact h.mono (by intro r; cases r <;> decide) (by decide) (by decide) (by decide) (by intro i k hk; simp only [rtTaint,VG.Slots.has_empty,Bool.false_eq_true] at hk) (by decide) (by decide) (by decide) (by decide)

 theorem sizeChoice_relCT (K : Nat) : RelCT isa (VG.X86.Taint.Agree rtTaint) (.block (sizeChoice K))
    (fun s t => VG.X86.Taint.Agree rtTaint s t ∧ s.zf=t.zf) := by
  intro s t tr ur sf tf h es et
  have pair := VG.Taint.check_sound (A:=taint) (sizeChoice_check K) h es et
  exact ⟨pair.1,sizeTaint_forget pair.2,(pair.2.rf.2 rfl).2.1⟩
 theorem aliasChoice_relCT : RelCT isa (VG.X86.Taint.Agree rtTaint) (.block aliasChoice)
    (fun s t => VG.X86.Taint.Agree rtTaint s t ∧ s.zf=t.zf) := by
  intro s t tr ur sf tf h es et
  have pair := VG.Taint.check_sound (A:=taint) aliasChoice_check h es et
  exact ⟨pair.1,aliasTaint_forget pair.2,(pair.2.rf.2 rfl).2.1⟩

end VG.Proof.Mont.X86.StaticSquare
