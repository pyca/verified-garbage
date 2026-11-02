module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.TimeCheck
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Impl.Mont.X86.MulRt
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
meta import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT

/-! # Constant-time public dispatch over the fixed and runtime square paths -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont.X86.Rt

-- Public flags at the fixed-width dispatch points. These helpers have one caller.
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



 theorem oldSquare_relCT : RelCT isa (VG.X86.Taint.Agree rtTaint) Impl.Mont.X86.Rt.Square.square (fun _ _ => True) :=
  VG.RelCT.taint (A:=sseTaint) rtTaint (fun _ _ h => h) (by taint_decide)
 theorem scalar_relCT : RelCT isa (VG.X86.Taint.Agree rtTaint) Impl.Mont.X86.Rt.scalarBody (fun _ _ => True) :=
  VG.RelCT.taint (A:=taint) rtTaint (fun _ _ h => h) (by taint_decide)

 theorem selectSize_relCT (K : Nat) {fallback : Prog isa}
    (body : RelCT isa (VG.X86.Taint.Agree rtTaint) (Impl.Mont.X86.Rt.StaticSquare.square K) (fun _ _ => True))
    (other : RelCT isa (VG.X86.Taint.Agree rtTaint) fallback (fun _ _ => True)) :
    RelCT isa (VG.X86.Taint.Agree rtTaint) (Impl.Mont.X86.Rt.StaticSquare.selectSize K fallback) (fun _ _ => True) := by
  unfold Impl.Mont.X86.Rt.StaticSquare.selectSize
  refine VG.RelCT.seq (sizeChoice_relCT K) ?_
  refine VG.RelCT.ite (fun _ _ h => h.2) ?_ ?_
  · exact body.mono (fun _ _ h => h.1.1) (fun _ _ _ => trivial)
  · exact other.mono (fun _ _ h => h.1.1) (fun _ _ _ => trivial)

 theorem dispatch_relCT : RelCT isa (VG.X86.Taint.Agree rtTaint) Impl.Mont.X86.Rt.StaticSquare.dispatch (fun _ _ => True) := by
  obtain ⟨_, square32_check⟩ := square32_check
  obtain ⟨_, square48_check⟩ := square48_check
  obtain ⟨_, square64_check⟩ := square64_check
  obtain ⟨_, square96_check⟩ := square96_check
  obtain ⟨_, square128_check⟩ := square128_check
  unfold Impl.Mont.X86.Rt.StaticSquare.dispatch
  refine VG.RelCT.seq aliasChoice_relCT ?_
  refine VG.RelCT.ite (fun _ _ h => h.2) ?_ ?_
  · exact (selectSize_relCT 32 (VG.RelCT.taint (A:=taint) rtTaint (fun _ _ h => h) square32_check)
      (selectSize_relCT 48 (VG.RelCT.taint (A:=taint) rtTaint (fun _ _ h => h) square48_check)
      (selectSize_relCT 64 (VG.RelCT.taint (A:=taint) rtTaint (fun _ _ h => h) square64_check)
      (selectSize_relCT 96 (VG.RelCT.taint (A:=taint) rtTaint (fun _ _ h => h) square96_check)
        (selectSize_relCT 128 (VG.RelCT.taint (A:=taint) rtTaint (fun _ _ h => h) square128_check) oldSquare_relCT))))).mono (fun _ _ h => h.1.1) (fun _ _ _ => trivial)
  · exact scalar_relCT.mono (fun _ _ h => h.1.1) (fun _ _ _ => trivial)

 theorem constantTime : ConstantTime isa (Proof.Rsa.MontMul.mulContract abi 0).pre
    (Proof.Rsa.MontMul.mulContract abi 0).pub Impl.Mont.X86.Rt.StaticSquare.dispatch := by
  apply VG.RelCT.constantTime
  exact dispatch_relCT.mono (fun _ _ ⟨h1,h2,hp⟩ =>
    rtTaint_agree (rtAbi_of h1) (rtAbi_of h2) (rt_publicArgs hp).1 (rt_publicArgs hp).2) (fun _ _ _ => trivial)

end VG.Proof.Mont.X86.StaticSquare
