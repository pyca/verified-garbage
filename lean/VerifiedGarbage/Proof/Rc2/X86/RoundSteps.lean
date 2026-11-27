module

public import VerifiedGarbage.Impl.Rc2.X86.Block
import VerifiedGarbage.Proof.Rc2.Word32
public import VerifiedGarbage.Proof.Rc2.X86.KeySteps
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86.Reduce

@[expose] public section

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

theorem addr_eq_def (x : BitVec 32) : addr32 x = x.setWidth 64 := rfl

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

theorem wordReg_separate (i : Nat) :
    wordReg i ≠ .esi ∧ wordReg i ≠ .edi ∧ wordReg i ≠ .ebp ∧ wordReg i ≠ .esp := by
  have fact : ∀ j < 4, wordReg j ≠ .esi ∧ wordReg j ≠ .edi ∧ wordReg j ≠ .ebp ∧ wordReg j ≠ .esp := by decide
  simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))

theorem selectWord (a b c : BitVec 32) :
    ((b ^^^ c) &&& a) ^^^ c = (a &&& b) + (~~~a &&& c) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
    cases a.getLsbD j <;> cases b.getLsbD j <;> cases c.getLsbD j <;> rfl
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hj, decide_true, Bool.true_and, BitVec.getLsbD_zero]
    cases a.getLsbD j <;> cases b.getLsbD j <;> cases c.getLsbD j <;> rfl

theorem rotation_bounds (i : Nat) : 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by
  have h : ∀ j < 4, 1 ≤ Spec.Rc2.rotation j ∧ Spec.Rc2.rotation j < 16 := by decide
  simpa only [Spec.Rc2.rotation, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem rotate16_ok (s : State) (r : Reg) (hr : r ≠ .esi) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ∃ s', runBlock isa (rotate16 r n) s = some s' ∧
      (s'.gpr r).setWidth 16 = ((s.gpr r).setWidth 16).rotateLeft n ∧ Keep [r, .esi] s s' := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega_using [hn, hn']
  have hright : 1 ≤ 16 - n ∧ 16 - n ≤ 31 := by omega_using [hn']
  refine ⟨_, by
    simp only [hleft, hright, and_self, rotate16, rr, runBlock_cons, runStep_some, runBlock_nil,
      reduceExec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, Ne.symm hr, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [Word32.maskWord]
    have h := congrArg (BitVec.setWidth 16) (Word32.rotateWord ((s.gpr r).setWidth 16) n hn hn')
    rw [Word32.maskWord, BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 32), BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 32), BitVec.setWidth_eq] at h
    exact h
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem mixSelect_ok (s : State) (i : Nat) :
    ∃ s', runBlock isa (mixSelect i) s = some s' ∧
      s'.gpr .esi = (s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
        (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))) ∧ Keep [.esi] s s' := by
  have h1 := (wordReg_separate (i + 1)).1
  have h3 := (wordReg_separate (i + 3)).1
  refine ⟨_, by
    simp only [mixSelect, rr, runBlock_cons, runStep_some, runBlock_nil,
      reduceExec, execAlu, readSrc, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, h1, h3, ite_false, ite_true]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self]; exact selectWord _ _ _
  · constructor
    · intro r hr
      have hn : r ≠ .esi := by simpa only [List.mem_singleton] using hr
      simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
    · rfl
    · rfl
    · rfl

theorem adjust_ok (sub : Bool) (s : State) (r : Reg) :
    ∃ s', runBlock isa (adjust sub r) s = some s' ∧
      s'.gpr r = (if sub then s.gpr r - s.gpr .esi else s.gpr r + s.gpr .esi) ∧
      Keep [r] s s' := by
  cases sub <;>
    refine ⟨_, by simp only [adjust, adjustOp, Bool.false_eq_true, ite_false, ite_true,
      runBlock_cons, reduceExec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]; rfl, ?_⟩
  all_goals
    constructor
    · exact gpr_setReg_self _ _ _
    · constructor
      · intro r' hr
        have hn : r' ≠ r := by simpa only [List.mem_singleton] using hr
        simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
      · rfl
      · rfl
      · rfl

end VG.Proof.Rc2.X86
