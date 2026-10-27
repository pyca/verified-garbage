module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelRun
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# A round

`roundBody_ok`: the round function (`feistel_ok`) and the half swap, the
standard DES round; `roundStep_ok`: with the next key and the round counted.
Neither writes memory.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.TripleDes.RISCV64

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) :=
  runBlock_append' a b s

/-- The registers the half swap keeps. -/
def roundOuterKept : List Reg :=
  [.ra, .s0, .s1, .s2, .s3, .s4, .s11, .a0, kp, cnt, kstep, passes]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr lReg = s.gpr rReg ∧ s'.gpr rReg = s.gpr lReg ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  let s₁ := s.write .t0 (s.gpr lReg + BitVec.ofInt 64 0)
  let s₂ := s₁.write lReg (s₁.gpr rReg + BitVec.ofInt 64 0)
  let s₃ := s₂.write rReg (s₂.gpr .t0 + BitVec.ofInt 64 0)
  refine ⟨s₃, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [swapHalves, movR, movR, movR, runBlock_cons, exec_addi (by decide), runStep_some,
      runBlock_cons, exec_addi (by decide), runStep_some, runBlock_cons, exec_addi (by decide),
      runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, gpr_write, lReg, rReg, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt_ofNat, BitVec.add_zero]
  · simp only [s₃, s₂, s₁, gpr_write, lReg, rReg, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt_ofNat, BitVec.add_zero]
  · intro q hq
    have hne : q ≠ .t0 ∧ q ≠ lReg ∧ q ≠ rReg := by revert hq; cases q <;> decide
    simp only [s₃, s₂, s₁, gpr_write, hne.1, hne.2.1, hne.2.2, ite_false]

/-- One full Feistel round: the round function and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr lReg = l.setWidth 64) (hr : s.gpr rReg = r.setWidth 64)
    (hk : s.mem.readW (s.gpr kp) 64 = k) (hready : FeiReady s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr lReg = r.setWidth 64 ∧
      s'.gpr rReg = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, sp₁, mem₁, keep₁⟩ :=
    feistel_ok s hready l r hl hr hread hal
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, mem₂.trans mem₁, ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ rReg (by decide)).trans hr)
  · rw [right]; exact value.trans (by rw [show s.gpr .a3 = s.gpr kp from rfl, hk])
  · intro q hq
    have hq' : q ∈ feistelKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')

/-- The registers a round and the step to the next keep. -/
def roundStepKept : List Reg := [.ra, .s0, .s1, .s2, .s3, .s4, .s11, .a0, kstep, passes]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n + BitVec.ofInt 64 (-1)) != 0) = decide (n ≠ 1) := by
  decide +kernel

theorem roundAdvance_ok (s : State) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr kp = s.gpr kp + s.gpr kstep ∧
      s'.gpr cnt = s.gpr cnt + BitVec.ofInt 64 (-1) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ cnt → r ≠ kp → s'.gpr r = s.gpr r) := by
  let s₁ := s.write kp (s.gpr kp + s.gpr kstep)
  let s₂ := s₁.write cnt (s₁.gpr cnt + BitVec.ofInt 64 (-1))
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [roundAdvance, runBlock_cons, exec_add, runStep_some, runBlock_cons,
      exec_addi (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, kp, cnt, kstep, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, kp, cnt, reduceCtorEq, ite_true, ite_false]
  · intro r h16 h17
    simp only [s₂, s₁, gpr_write, h16, h17, ite_false]

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr lReg = l.setWidth 64) (hr : s.gpr rReg = r.setWidth 64)
    (hk : s.mem.readW (s.gpr kp) 64 = k) (hready : FeiReady s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0)
    (hcount : s.gpr cnt = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr lReg = r.setWidth 64 ∧
      s'.gpr rReg = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr kp = s.gpr kp + s.gpr kstep ∧
      s'.gpr cnt = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero cnt) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, mem₁, keep₁⟩ :=
    roundBody_ok s l r k hl hr hk hready hread hal
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := roundAdvance_ok s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr cnt = BitVec.ofNat 64 n := (keep₁ cnt (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁,
    mem₂.trans mem₁, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ lReg (by decide) (by decide)).trans left₁
  · exact (keep₂ rReg (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ kp (by decide), keep₁ kstep (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.RISCV64.eval (.nonzero cnt) s₂ = _
    simp only [VG.RISCV64.eval, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ cnt ∧ q ≠ kp := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')

end VG.Proof.TripleDes.RISCV64
