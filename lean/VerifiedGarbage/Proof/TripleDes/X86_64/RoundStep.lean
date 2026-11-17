module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.TripleDes.X86_64.Box
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.TripleDes.X86_64.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `TripleDes.X86_64.PassSteps`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

def countAddr (s : State) : Addr := s.gpr .rdx + BitVec.ofNat 64 56

theorem roundCountAdvance_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (countAddr s) 8)
    (hwrite : InRegions s.wr (countAddr s) 8) :
    ∃ s', runBlock isa roundCountAdvance s = some s' ∧
      s'.mem = s.mem.writeW (countAddr s) (s.mem.readW (countAddr s) 64 - 1) ∧
      s'.zf = some ((s.mem.readW (countAddr s) 64 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  unfold countAddr at hread hwrite
  have hoff : BitVec.ofInt 64 (Int.ofNat 56) = BitVec.ofNat 64 56 := rfl
  refine ⟨_, by
    simp only [roundCountAdvance, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, memOp, hoff, State.load64, State.store64,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, reduceCtorEq, ite_false, ite_true,
      hread, hwrite, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [zf_setReg, zf_arithFlags]
    rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

def stepAddr (s : State) : Addr := s.gpr .rdx + BitVec.ofNat 64 448

/-- The key pointer advanced by the step in scratch slot 56. -/
theorem pointerAdvance_ok (s : State) (hread : InRegions (s.rd ++ s.wr) (stepAddr s) 8) :
    ∃ s', runBlock isa
      [.mov .rax (.mem (memOp .rdx 448)), .alu .add .rdi (.reg .rax)] s = some s' ∧
      s'.gpr .rdi = s.gpr .rdi + s.mem.readW (stepAddr s) 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → s'.gpr r = s.gpr r) := by
  unfold stepAddr at hread
  have hoff : BitVec.ofInt 64 (Int.ofNat 448) = BitVec.ofNat 64 448 := rfl
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, memOp, hoff, State.load64,
      gpr_setReg, reduceCtorEq, ite_false, ite_true,
      hread, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rfl
  · simp only [mem_setReg, mem_arithFlags]
  · simp only [rd_setReg, rd_arithFlags]
  · simp only [wr_setReg, wr_arithFlags]
  · intro r hrax hrdi
    simp only [gpr_setReg, gpr_arithFlags, hrax, hrdi, ite_false]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) == 0) = decide (n = 1) := by
  decide +kernel

theorem countWrite_frame (m : Mem) (p : Addr) (v : BitVec 64) :
    Frame [⟨p, 8⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

theorem roundAdvance_ok (s : State)
    (hstep : InRegions (s.rd ++ s.wr) (stepAddr s) 8)
    (hread : InRegions (s.rd ++ s.wr) (countAddr s) 8)
    (hwrite : InRegions s.wr (countAddr s) 8) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr .rdi = s.gpr .rdi + s.mem.readW (stepAddr s) 64 ∧
      s'.mem = s.mem.writeW (countAddr s) (s.mem.readW (countAddr s) 64 - 1) ∧
      s'.zf = some ((s.mem.readW (countAddr s) 64 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, ptr₁, mem₁, rd₁, wr₁, keep₁⟩ := pointerAdvance_ok s hstep
  have haddr : countAddr s₁ = countAddr s := by
    simp only [countAddr, keep₁ .rdx (by decide) (by decide)]
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (countAddr s₁) 8 := by
    rw [rd₁, wr₁, haddr]; exact hread
  have hwrite₁ : InRegions s₁.wr (countAddr s₁) 8 := by
    rw [wr₁, haddr]; exact hwrite
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ := roundCountAdvance_ok s₁ hread₁ hwrite₁
  refine ⟨s₂, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩
  · simp only [roundAdvance, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .rdi (by decide)).trans ptr₁
  · rw [mem₂, mem₁, haddr]
  · rw [flag₂, mem₁, haddr]
  · exact fun r hrax hrdi => (keep₂ r hrax).trans (keep₁ r hrax hrdi)

end VG.Proof.TripleDes.X86_64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64

/-- What the rounds write: the round counter and the S-box spills. -/
def roundRegion (s : State) : Region := ⟨s.gpr .rdx + BitVec.ofNat 64 56, 392⟩

/-- What a pass writes: the rounds' region, the key step and the passes left. -/
def workRegion (s : State) : Region := ⟨s.gpr .rdx + BitVec.ofNat 64 56, 408⟩

theorem round_sub_work (s : State) : Region.Sub (roundRegion s) (workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem step_round_disjoint (s : State) :
    (⟨stepAddr s, 8⟩ : Region).Disjoint (roundRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem step_spill_disjoint (s : State) :
    (⟨stepAddr s, 8⟩ : Region).Disjoint (spillRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem count_spill_disjoint (s : State) :
    (⟨countAddr s, 8⟩ : Region).Disjoint (spillRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem spill_sub_work (s : State) : Region.Sub (spillRegion s) (roundRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem count_sub_work (s : State) : Region.Sub ⟨countAddr s, 8⟩ (roundRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r12 = l.setWidth 64) (hr : s.gpr .r13 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .rdi) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8)
    (hsep : (⟨s.gpr .rdi, 8⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.mem.readW (countAddr s) 64 = BitVec.ofNat 64 n)
    (hcountRead : InRegions (s.rd ++ s.wr) (countAddr s) 8)
    (hcountWrite : InRegions s.wr (countAddr s) 8)
    (hstep : InRegions (s.rd ++ s.wr) (stepAddr s) 8) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr .r12 = r.setWidth 64 ∧
      s'.gpr .r13 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .rdi = s.gpr .rdi + s.mem.readW (stepAddr s) 64 ∧
      s'.mem.readW (countAddr s') 64 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.rsi, .rdx, .rsp], s'.gpr q = s.gpr q) ∧
      Frame [roundRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  have haddr : countAddr s₁ = countAddr s := by
    simp only [countAddr, keep₁ .rdx (by decide)]
  have hcount₁ : s₁.mem.readW (countAddr s₁) 64 = BitVec.ofNat 64 n := by
    rw [haddr]
    refine Eq.trans (frame₁.readW (r := ⟨countAddr s, 8⟩) ?_ ?_ (by decide)) hcount
    · exact Region.contains_self _ _
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact count_spill_disjoint s
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (countAddr s₁) 8 := by
    rw [rd₁, wr₁, haddr]; exact hcountRead
  have hwrite₁ : InRegions s₁.wr (countAddr s₁) 8 := by
    rw [wr₁, haddr]; exact hcountWrite
  have hstepAddr : stepAddr s₁ = stepAddr s := by
    simp only [stepAddr, keep₁ .rdx (by decide)]
  have hstep₁ : InRegions (s₁.rd ++ s₁.wr) (stepAddr s₁) 8 := by
    rw [rd₁, wr₁, hstepAddr]; exact hstep
  have hstepVal : s₁.mem.readW (stepAddr s₁) 64 = s.mem.readW (stepAddr s) 64 := by
    rw [hstepAddr]
    refine frame₁.readW (r := ⟨stepAddr s, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    exact step_spill_disjoint s
  obtain ⟨s₂, run₂, ptr₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ :=
    roundAdvance_ok s₁ hstep₁ hread₁ hwrite₁
  have hcountAddr₂ : countAddr s₂ = countAddr s₁ := by
    simp only [countAddr, keep₂ .rdx (by decide) (by decide)]
  have hwork : roundRegion s₁ = roundRegion s := by
    simp only [roundRegion, keep₁ .rdx (by decide)]
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r12 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r13 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .rdi (by decide), hstepVal]
  · rw [hcountAddr₂, mem₂, Mem.readW_writeW_self64, hcount₁, hsub]
  · change VG.X86_64.eval .ne s₂ = some (decide (n ≠ 1))
    simp only [VG.X86_64.eval, flag₂, hcount₁, hzero, Option.map_some]
    simp
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .rax ∧ q ≠ .rdi := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · have hf₁ : Frame [roundRegion s] s.mem s₁.mem := frame₁.sub (by
      intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, spill_sub_work s⟩)
    have hf₂ := countWrite_frame s₁.mem (countAddr s₁) (s₁.mem.readW (countAddr s₁) 64 - 1)
    have hf₂' : Frame [roundRegion s₁] s₁.mem s₂.mem := by
      rw [mem₂]
      exact hf₂.sub (by
        intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact ⟨_, List.mem_singleton_self _, count_sub_work s₁⟩)
    rw [hwork] at hf₂'
    exact hf₁.trans hf₂'

end VG.Proof.TripleDes.X86_64
