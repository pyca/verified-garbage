module

import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.X86.Mmx
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Code

/-!
# x86 (32-bit): MXCSR's value outside MCDT frames never changes

No instruction, call, return or frame changes `State.mxcsr`, so neither does
a run (`Exec.mxcsr`), as `Exec.syms` for the statics.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86

theorem setReg_mxcsr (s : State) (r : Reg) (v : BitVec 32) : (s.setReg r v).mxcsr = s.mxcsr := rfl

theorem exec_mxcsr {i : Instr} {s s' : State} (h : exec i s = some s') : s'.mxcsr = s.mxcsr := by
  cases i with
  | store m r | store8 m r | movdquStore m r | movqStore m r =>
    simp only [exec, State.store32, State.store8, State.store128, State.store64] at h
    split at h <;> cases h; rfl
  | mov _ _ | movzx8 _ _ | movdquLoad _ _ | movqLoad _ _ =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | shift op _ n =>
    simp only [exec, execShift] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl
    · cases h
  | xop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [SseTaint.XOp.exec_eq op s]
  | mop op => rw [MOp.exec_eq h]
  | mmxStore m r =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    simp only [State.store64] at h
    split at h <;> cases h; rfl
  | symPush | push | pop | alloc | free | mmxEnter | emms | mcdtEnter | mcdtLeave =>
    simp only [exec, reduceCtorEq] at h
  | pmuludq =>
    simp only [exec] at h
    split at h <;> cases h; rfl
  | _ => simp only [exec, Option.some.injEq] at h; subst h; rfl

theorem pushRegs_mxcsr (t : State) (rs : List Reg) : (pushRegs t rs).mxcsr = t.mxcsr := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih => exact (ih _).trans rfl

theorem push_mxcsr {i : Instr} {s s' : State} (h : push i s = some s') : s'.mxcsr = s.mxcsr := by
  cases i <;> simp only [push, reduceCtorEq] at h <;> split at h <;> cases h <;>
    first | rfl | exact pushRegs_mxcsr _ _

theorem pop_mxcsr {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') : s'.mxcsr = s₂.mxcsr := by
  have hp : ∀ (k : Nat) (r : Reg) (t : State), (popReg t r k).mxcsr = t.mxcsr := by
    intro k; induction k with
    | zero => intro r t; rfl
    | succ k ih => intro r t; exact (ih _ _).trans rfl
  cases j <;> simp only [pop, reduceCtorEq] at h <;> split at h <;> cases h <;>
    first | rfl | exact hp _ _ _

theorem execBlock_mxcsr : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.mxcsr = s.mxcsr
  | [], _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, s, s', t, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h₂, e₂⟩ := Option.map_eq_some_iff.mp h
      cases e₂
      exact (execBlock_mxcsr h₂).trans (exec_mxcsr e)

theorem Exec.mxcsr {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.mxcsr = s.mxcsr := by
  induction h with
  | block e => exact execBlock_mxcsr e
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | iteT _ _ ih | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | call e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih
  | frame e₁ _ e₂ ih => exact (pop_mxcsr e₂).trans (ih.trans (push_mxcsr e₁))

end VG.Proof.Mont.X86.Sse2
