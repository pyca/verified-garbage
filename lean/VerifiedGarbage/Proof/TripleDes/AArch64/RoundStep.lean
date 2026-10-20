module
public import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
public import VerifiedGarbage.Proof.TripleDes.AArch64.Spills
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def roundStepKept : List Reg := [.x0, .x1, .x2, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) != 0) = decide (n ≠ 1) := by
  decide +kernel

/-- The key step of the pass, in the low lane of `v0`. -/
def stepOf (s : State) : BitVec 64 := vdword (s.v .v0) 0

/-- The passes left, in the low lane of `v1`. -/
def passesOf (s : State) : BitVec 64 := vdword (s.v .v1) 0

theorem roundBody_noV : roundBody.all (fun i => vdstOf i == none) = true := by
  decide +kernel

theorem roundAdvance_ok (s : State) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr .x22 = s.gpr .x22 + stepOf s ∧
      s'.gpr .x21 = s.gpr .x21 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.v = s.v ∧
      (∀ r, r ≠ .x3 → r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .x .x3 (vdword (s.v .v0) 0)
  let s₂ := s₁.write .x .x22 (s₁.read .x .x22 + s₁.read .x .x3)
  let s₃ := s₂.write .x .x21 (s₂.read .x .x21 - BitVec.ofNat _ 1)
  refine ⟨s₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rw [roundAdvance, runBlock_cons, show exec (.umov .x .x3 .v0 0) s = some s₁ from rfl,
      runStep_some, runBlock_cons, VG.AArch64.exec_add, runStep_some, runBlock_cons,
      VG.AArch64.exec_subImm_x (by decide), runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, stepOf, State.read, BitVec.setWidth_eq, gpr_write, reduceCtorEq,
      ite_true, ite_false]
  · simp only [s₃, s₂, s₁, State.read, BitVec.setWidth_eq, gpr_write, reduceCtorEq,
      ite_true, ite_false]
    rfl
  · simp only [s₃, s₂, s₁, rd_write]
  · simp only [s₃, s₂, s₁, wr_write]
  · simp only [s₃, s₂, s₁, sp_write]
  · simp only [s₃, s₂, s₁, mem_write]
  · intro r hr₁ hr₂ hr₃
    simp only [s₃, s₂, s₁, gpr_write, hr₁, hr₂, hr₃, ite_false]

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .x19 = l.setWidth 64) (hr : s.gpr .x20 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .x22) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8)
    (hsep : (⟨s.gpr .x22, 8⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.gpr .x21 = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr .x19 = r.setWidth 64 ∧
      s'.gpr .x20 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .x22 = s.gpr .x22 + stepOf s ∧ s'.v = s.v ∧
      s'.gpr .x21 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero .x .x21) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, sp₂, mem₂, v₂, keep₂⟩ := roundAdvance_ok s₁
  have v₁ : s₁.v = s.v := VG.AArch64.Tbl.runBlock_v roundBody_noV run₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .x21 = BitVec.ofNat 64 n := (keep₁ .x21 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, v₂.trans v₁, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁,
    ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .x19 (by decide) (by decide) (by decide)).trans left₁
  · exact (keep₂ .x20 (by decide) (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .x22 (by decide), stepOf, stepOf, v₁]
  · rw [count₂, hcount₁, hsub]
  · change VG.AArch64.eval (.nonzero .x .x21) s₂ = _
    simp only [VG.AArch64.eval, State.read, BitVec.setWidth_eq, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .x3 ∧ q ≠ .x21 ∧ q ≠ .x22 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2.1 hneq.2.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.AArch64
