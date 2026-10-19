module

public import VerifiedGarbage.Proof.Framework.Arm.TaintMono
import VerifiedGarbage.Proof.Framework.Arm.Syms
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target

/-!
# ARMv7 taint tracking with the addresses of statics

`taintS`, but the addresses of the statics named in `L` are public (as a
contract with those tables of constants says: `Abi.withConsts`), so the
register `adrSym` puts one in is public, and the code may address the table
from it (`taintSym L`). The analysis sees such an `adrSym d n` as
`movw d, #0` (`Instr.symMov`), a public constant, which writes `d` and
nothing else, as `adrSym` does: both runs give `d` the static's address, the
same in both. No instruction changes the addresses (`exec_syms`). Summaries
(`taint_summary`) and checks with them (`taint_decide_sum`) work as with
`taintS`: the order and the frame are its.
-/

@[expose] public section

namespace VG.Arm

/-- An instruction as `taintSym L` analyses it: `adrSym d n` of a static of
`L` as `movw d, #0`, a public constant; the others as they are. -/
def Instr.symMov (L : List String) : Instr → Instr
  | .adrSym d n => if n ∈ L then .movw d 0 else .adrSym d n
  | i => i

namespace Taint

/-- `Agree`, and the statics of `L` at the same addresses. -/
def AgreeS (L : List String) (τ : T) (s₁ s₂ : State) : Prop :=
  Agree τ s₁ s₂ ∧ ∀ n ∈ L, s₁.syms n = s₂.syms n

/-- `stepKD`, with the address of a static of `L` public. -/
def stepS (L : List String) (τ : T) (i : Instr) : Option T := stepKD τ (i.symMov L)

theorem stepS_sound {L : List String} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeS L τ s₁ s₂) (hs : stepS L τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ AgreeS L τ' s₁' s₂' := by
  have hsy : ∀ n ∈ L, s₁'.syms n = s₂'.syms n := fun n hn => by
    rw [exec_syms e₁, exec_syms e₂]; exact ha.2 n hn
  unfold stepS at hs
  by_cases hl : ∃ d n, i = .adrSym d n ∧ n ∈ L
  · obtain ⟨d, n, rfl, hn⟩ := hl
    simp only [Instr.symMov, hn, ↓reduceIte] at hs
    have hs' : some { τ with regs := set τ d true, bases := kill τ d } = some τ' := by
      rw [← setK_eq, ← killK_eq]; exact hs
    cases hs'
    refine ⟨rfl, ha.1.write (i := .adrSym d n) rfl e₁ e₂ ?_ rfl rfl rfl rfl (fun _ h => h), hsy⟩
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨regs_set (d := d) (p := true) ha.1.rf.1 fun _ => ha.2 n hn, fun hf => ha.1.rf.2 hf⟩
  · have e : i.symMov L = i := by
      cases i <;> simp only [Instr.symMov]
      rename_i d n
      exact ite_eq_right_of_eq_false _ _ (eq_false fun hn => hl ⟨d, n, rfl, hn⟩)
    rw [e] at hs
    exact ⟨(taintS.step_sound ha.1 hs e₁ e₂).1, (taintS.step_sound ha.1 hs e₁ e₂).2, hsy⟩

end Taint

/-- Taint tracking for ARMv7 code that addresses the statics `L`, whose
addresses are public. -/
def taintSym (L : List String) : VG.Taint isa where
  T := Taint.T
  Agree := Taint.AgreeS L
  step := Taint.stepS L
  step_sound := Taint.stepS_sound
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
  -- Frames are not analysed.
  push := taintS.push
  push_sound _ h := by cases h
  pop := taintS.pop
  pop_sound _ h := by cases h

open VG.Taint in
instance (L : List String) : LeFrame (taintSym L) where
  le_trans := LeFrame.le_trans (A := taintS)
  le_right := LeFrame.le_right (A := taintS)
  step i h hs := LeFrame.step (A := taintS) (i.symMov L) h hs
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
  keeps F i := LeFrame.keeps (A := taintS) F (i.symMov L)
  keepsCall := LeFrame.keepsCall (A := taintS)
  keeps_bot i := LeFrame.keeps_bot (A := taintS) (i.symMov L)
  keepsCall_bot := LeFrame.keepsCall_bot (A := taintS)
  step_keeps i hk hΦF hΦ hs := LeFrame.step_keeps (A := taintS) (i.symMov L) hk hΦF hΦ hs
  call_keeps := LeFrame.call_keeps (A := taintS)
  ret_keeps := LeFrame.ret_keeps (A := taintS)
  push_keeps _ _ _ _ hs := by cases hs
  pop_keeps _ _ _ _ hs := by cases hs

end VG.Arm
