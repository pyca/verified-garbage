module

import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Square.Step
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.X86.Words

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def ctl (r : Reg) : List Instr :=
  [.alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg r)]

def addPtr (s : State) (r : Reg) (v : BitVec 32) : State :=
  (arithFlags s (s.gpr r + v) (2^32 ≤ (s.gpr r).toNat+v.toNat)
    (addOverflow (s.gpr r) v (s.gpr r+v))).setReg r (s.gpr r+v)

def subPtr (s : State) (r : Reg) (v : BitVec 32) : State :=
  (arithFlags s (s.gpr r - v) ((s.gpr r).toNat < v.toNat)
    (subOverflow (s.gpr r) v (s.gpr r-v))).setReg r (s.gpr r-v)

def cmpReg (s : State) (l r : Reg) : State :=
  arithFlags s (s.gpr l-s.gpr r) ((s.gpr l).toNat < (s.gpr r).toNat)
    (subOverflow (s.gpr l) (s.gpr r) (s.gpr l-s.gpr r))

def ctlState (s : State) (r : Reg) : State := cmpReg (subPtr (addPtr s .ecx 4) .ebp 4) .ecx r

theorem run_ctl (s : State) (r : Reg) : runBlock isa (ctl r) s = some (ctlState s r) := by
  rfl

theorem ctl_values (s : State) (r : Reg) (hr : r = .ebp ∨ r = .ebx) :
    (ctlState s r).gpr .ecx = s.gpr .ecx + 4 ∧
    (ctlState s r).gpr .ebp = s.gpr .ebp - 4 ∧
    (ctlState s r).cf = some (decide ((s.gpr .ecx+4).toNat <
      (if r = .ebp then s.gpr .ebp-4 else s.gpr r).toNat)) ∧
    (ctlState s r).xmm = s.xmm ∧
    (ctlState s r).mem = s.mem ∧
    Keeps [.ecx, .ebp] s (ctlState s r) := by
  have g : ∀ j, (ctlState s r).gpr j =
      if j = .ebp then s.gpr .ebp-4 else if j = .ecx then s.gpr .ecx+4 else s.gpr j := by
    intro j
    simp [ctlState, cmpReg, subPtr, addPtr, arithFlags, State.setReg, State.setFlags]
  refine ⟨g .ecx, g .ebp, ?_, rfl, rfl, ?_⟩
  · rcases hr with rfl | rfl <;>
      simp [ctlState, cmpReg, subPtr, addPtr, arithFlags, State.setReg, State.setFlags]
  · refine ⟨?_, rfl, rfl⟩
    intro j hj
    rw [g]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [hj.1, hj.2]

end VG.Proof.Mont.X86.Square
