module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.TaintOps
import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.TaintOps
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# x86-64 taint tracking with MXCSR public

`taintS`, whose states also agree on MXCSR (`taintMx`), as two runs from
states that agree on a contract's public data do (`abi.pub`): no instruction
the analysis allows writes MXCSR (it rejects `ldmxcsr`), so they keep
agreeing. The analysis itself learns nothing from it (`stmxcsr` stores a
secret, as in `taintS`); what it is for is operations (`Taint.Op`) whose
timing depends on MXCSR, such as a call of `vg_mcdt_enter`
(`Proof/Mcdt/X86_64/Op.lean`), whose soundness needs both runs to start
with the same MXCSR. Summaries (`taint_summary_ops`) and checks with them
(`taint_decide_ops`) work as with `taintS`: the order and the frame are its.
-/

@[expose] public section

namespace VG.X86_64

namespace Taint

/-- `Agree`, and the same MXCSR. -/
def AgreeMx (τ : T) (s₁ s₂ : State) : Prop := Agree τ s₁ s₂ ∧ s₁.mxcsr = s₂.mxcsr

/-- `stepKeep`, but for `ldmxcsr`, which fails. -/
def stepMx (τ : T) : Instr → Option T
  | .ldmxcsr _ => none
  | i => stepKeep τ i

theorem stepMx_eq {τ : T} {i : Instr} {τ' : T} (h : stepMx τ i = some τ') :
    loadsMxcsr i = false ∧ taintS.step τ i = some τ' := by
  cases i <;> first | cases h | exact ⟨rfl, h⟩

theorem stepMx_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeMx τ s₁ s₂) (hs : stepMx τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ AgreeMx τ' s₁' s₂' := by
  obtain ⟨hl, hs⟩ := stepMx_eq hs
  obtain ⟨h₁, h₂⟩ := taintS.step_sound ha.1 hs e₁ e₂
  exact ⟨h₁, h₂, by rw [exec_mxcsr hl e₁, exec_mxcsr hl e₂, ha.2]⟩

end Taint

/-- Taint tracking for x86-64 with MXCSR the same in both runs. -/
def taintMx : VG.Taint isa where
  T := Taint.T
  Agree := Taint.AgreeMx
  step := Taint.stepMx
  step_sound := Taint.stepMx_sound
  condPub := taintS.condPub
  cond_sound h := taintS.cond_sound h.1
  meet := taintS.meet
  meet_left h := ⟨taintS.meet_left h.1, h.2⟩
  meet_right h := ⟨taintS.meet_right h.1, h.2⟩
  le := taintS.le
  le_sound hle h := ⟨taintS.le_sound hle h.1, h.2⟩
  call := taintS.call
  call_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := taintS.call_sound h.1 hs e₁ e₂
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨a, b, h.2⟩
  ret := taintS.ret
  ret_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := taintS.ret_sound h.1 hs e₁ e₂
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨a, b, h.2⟩
  push := taintS.push
  push_sound _ h := by cases h
  pop := taintS.pop
  pop_sound _ h := by cases h

theorem taintMx_step_mono {τ σ τ' : Taint.T} (i : Instr) (h : taintS.le τ σ = true)
    (hs : taintMx.step τ i = some τ') : ∃ σ', taintMx.step σ i = some σ' ∧ taintS.le τ' σ' = true := by
  obtain ⟨hl, hs⟩ := Taint.stepMx_eq hs
  obtain ⟨σ', h₁, h₂⟩ := VG.Taint.LeFrame.step (A := taintS) i h hs
  refine ⟨σ', ?_, h₂⟩
  cases i <;> first | exact h₁ | cases hl

open VG.Taint in
instance : LeFrame taintMx where
  le_trans := LeFrame.le_trans (A := taintS)
  le_right := LeFrame.le_right (A := taintS)
  step := taintMx_step_mono
  condPub := LeFrame.condPub (A := taintS)
  meet := LeFrame.meet (A := taintS)
  call := LeFrame.call (A := taintS)
  ret := LeFrame.ret (A := taintS)
  push _ _ hs := by cases hs
  pop _ _ hs := by cases hs
  join := LeFrame.join (A := taintS)
  bot := LeFrame.bot (A := taintS)
  join_lub := LeFrame.join_lub (A := taintS)
  frameOf := LeFrame.frameOf (A := taintS)
  frame_le_left := LeFrame.frame_le_left (A := taintS)
  frame_le_right := LeFrame.frame_le_right (A := taintS)
  frame_mono := LeFrame.frame_mono (A := taintS)
  le_frame := LeFrame.le_frame (A := taintS)
  le_meet := LeFrame.le_meet (A := taintS)
  bot_le := LeFrame.bot_le (A := taintS)
  bot_valid := LeFrame.bot_valid (A := taintS)
  keeps := LeFrame.keeps (A := taintS)
  keepsCall := LeFrame.keepsCall (A := taintS)
  keeps_bot := LeFrame.keeps_bot (A := taintS)
  keepsCall_bot := LeFrame.keepsCall_bot (A := taintS)
  step_keeps i hk hΦF hΦ hs := LeFrame.step_keeps (A := taintS) i hk hΦF hΦ (Taint.stepMx_eq hs).2
  call_keeps := LeFrame.call_keeps (A := taintS)
  ret_keeps := LeFrame.ret_keeps (A := taintS)
  push_keeps _ _ _ _ hs := by cases hs
  pop_keeps _ _ _ _ hs := by cases hs

/-- What two runs end agreeing on, in `taintMx`, includes MXCSR. -/
theorem taintMx_mx {s₁ s₂ : State} (h : ∃ τ, taintMx.Agree τ s₁ s₂) : s₁.mxcsr = s₂.mxcsr :=
  let ⟨_, h⟩ := h; h.2

end VG.X86_64
