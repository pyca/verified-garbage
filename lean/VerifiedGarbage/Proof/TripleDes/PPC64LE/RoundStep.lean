module
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Spills

import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundBody
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Box
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE

/-- The registers a round and the step to the next keep. -/
def roundStepKept : List Reg := [.r2, .r3, .r4, .r5, .r18, .r19, .r31]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) != 0) = decide (n ≠ 1) := by
  decide +kernel

theorem roundAdvance_ok (s : State) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr .r17 = s.gpr .r17 + s.gpr .r18 ∧
      s'.gpr .r16 = s.gpr .r16 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r16 → r ≠ .r17 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r17 (s.gpr .r17 + s.gpr .r18)
  let s₂ := s₁.write .r16 (s₁.gpr .r16 - BitVec.ofNat 64 1)
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [roundAdvance, runBlock_cons, exec_add, runStep_some, runBlock_cons,
      exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
    rfl
  · intro r h16 h17
    simp only [s₂, s₁, gpr_write, h16, h17, ite_false]

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .r17) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8)
    (hsep : (⟨s.gpr .r17, 8⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.gpr .r16 = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr .r14 = r.setWidth 64 ∧
      s'.gpr .r15 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .r17 = s.gpr .r17 + s.gpr .r18 ∧
      s'.gpr .r16 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero .d .r16) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, mem₂, keep₂⟩ := roundAdvance_ok s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .r16 = BitVec.ofNat 64 n := (keep₁ .r16 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r14 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r15 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .r17 (by decide), keep₁ .r18 (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.PPC64LE.eval (.nonzero .d .r16) s₂ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .r16 ∧ q ≠ .r17 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.PPC64LE
