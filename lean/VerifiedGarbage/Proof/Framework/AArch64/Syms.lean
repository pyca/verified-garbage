module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# AArch64: the addresses of statics never change

No instruction, call, return or frame changes `State.syms`, the addresses of
the statics the code names (`adrSym`), so neither does a run (`Exec.syms`):
`WP.mono_syms` lets a proof use that the state after some code names the
same addresses as before it.

Likewise for PSTATE.DIT, which only `msr DIT` writes (`Instr.writesDit`):
code without it keeps the mode (`Exec.dit`), so leaves the same mode in two
runs from the same (`DitDet`), what a caller needs of a callee to relate the
mode of its two runs after the call, now that the mode is public
(`abi.pub`).
-/

@[expose] public section

namespace VG.AArch64

/-- What no instruction changes: SP, the addresses of statics and the unknowns, and PSTATE.DIT
but by `msr DIT`, which gives it a value of its own. -/
theorem exec_fixed {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.sp = s.sp ∧ s'.syms = s.syms ∧ s'.unknowns = s.unknowns ∧
      (s'.dit = s.dit ∨ ∃ on, i = .msrDitImm on ∧ s'.dit = on) := by
  cases i with
  | msrDitImm on => obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, rfl, .inr ⟨on, rfl, rfl⟩⟩
  | str sz t n off | strb t n off | strq t n off =>
    simp only [reduceExec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | ldr sz t n off | ldrb t n off | ldrq t n off =>
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | ldrqTbl t n off name ws =>
    simp only [reduceExec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | vop op =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, _⟩, -, rfl⟩ := h; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | ldrSp t off =>
    obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | strSp t off =>
    obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
    simp only [State.store] at h
    split at h <;> cases h; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | ldp t1 t2 n off =>
    obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, -, _, -, rfl⟩ := h; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | stp t1 t2 n off =>
    obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
    simp only [Option.bind_eq_some_iff, State.store] at h
    obtain ⟨_, h₁, h₂⟩ := h
    split at h₁ <;> cases h₁; split at h₂ <;> cases h₂; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | ccmp sz n imm nzcv cond =>
    obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h; obtain rfl := Option.some.inj h
    split <;> exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | push _ | pop _ | alloc _ | free _ | blr _ => simp only [reduceExec, reduceCtorEq] at h
  | logicRor _ _ _ _ _ _ | bicRor _ _ _ _ _ | extr _ _ _ _ _ | addSp _ _ | addImm _ _ _ _
  | subImm _ _ _ _ | ror _ _ _ _ | lsr _ _ _ _ | lsl _ _ _ _ | movz _ _ _ _ | movk _ _ _ _
  | umov _ _ _ _ | ldrTbl _ _ _ _ _ _ =>
    obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h; obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl, .inl rfl⟩
  | _ => obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, rfl, .inl rfl⟩

theorem exec_syms {i : Instr} {s s' : State} (h : exec i s = some s') : s'.syms = s.syms :=
  (exec_fixed h).2.1

theorem push_syms {i : Instr} {s s' : State} (h : push i s = some s') : s'.syms = s.syms := by
  cases i <;> simp only [push] at h <;> (repeat' split at h) <;> simp_all <;> (subst h; rfl)

theorem pop_syms {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') : s'.syms = s₂.syms := by
  cases j <;> simp only [pop] at h <;> (repeat' split at h) <;> simp_all <;> (subst h; rfl)

theorem execBlock_syms : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.syms = s.syms
  | [], _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, s, s', t, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h₂, e₂⟩ := Option.map_eq_some_iff.mp h
      cases e₂
      exact (execBlock_syms h₂).trans (exec_syms e)

theorem Exec.syms {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.syms = s.syms := by
  induction h with
  | icall _ e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih
  | icallNext _ _ _ ih => exact ih
  | block e => exact execBlock_syms e
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | iteT _ _ ih | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | call e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih
  | frame e₁ _ e₂ ih => exact (pop_syms e₂).trans (ih.trans (push_syms e₁))

/-- The state after `c` names the same addresses of statics as before it. -/
theorem WP.mono_syms {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (k : ∀ s', Q s' → s'.syms = s.syms → R s') : WP isa c s R := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, k s' hq (Exec.syms he)⟩

/-- `Q` of the state after `c`, which may assume it names the same addresses
of statics as before. -/
theorem WP.of_syms {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => s'.syms = s.syms → Q s') : WP isa c s Q :=
  WP.mono_syms h fun _ hq sy => hq sy

/-! ## PSTATE.DIT -/

/-- Whether `i` writes PSTATE.DIT. -/
def Instr.writesDit : Instr → Bool
  | .msrDitImm _ => true
  | _ => false

theorem exec_dit {i : Instr} {s s' : State} (hi : i.writesDit = false) (h : exec i s = some s') :
    s'.dit = s.dit := by
  rcases (exec_fixed h).2.2.2 with e | ⟨_, rfl, -⟩
  · exact e
  · cases hi

theorem push_dit {i : Instr} {s s' : State} (h : push i s = some s') : s'.dit = s.dit := by
  cases i <;> simp only [push] at h <;> (repeat' split at h) <;> simp_all <;> (subst h; rfl)

theorem pop_dit {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') : s'.dit = s₂.dit := by
  cases j <;> simp only [pop] at h <;> (repeat' split at h) <;> simp_all <;> (subst h; rfl)

theorem execBlock_dit : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    (∀ i ∈ is, i.writesDit = false) → execBlock isa is s = some (s', t) → s'.dit = s.dit
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, s, s', t, hw, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h₂, e₂⟩ := Option.map_eq_some_iff.mp h
      cases e₂
      exact (execBlock_dit (fun j hj => hw j (List.mem_cons_of_mem _ hj)) h₂).trans
        (exec_dit (hw i (List.mem_cons_self ..)) e)

/-- Code that never writes PSTATE.DIT keeps it. -/
theorem Exec.dit {c : Prog isa} (hc : c.all (fun i => !i.writesDit) = true) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : s'.dit = s.dit := by
  induction h with
  | icall _ e₁ _ e₂ ih =>
    simp only [Code.all, Bool.and_eq_true] at hc
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih hc.1.2
  | icallNext _ _ _ ih => exact ih (by simp only [Code.all, Bool.and_eq_true] at hc ⊢; exact hc.2)
  | block e =>
    simp only [Code.all, List.all_eq_true, Bool.not_eq_true'] at hc
    exact execBlock_dit hc e
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.all, Bool.and_eq_true] at hc; exact (ih₂ hc.2).trans (ih₁ hc.1)
  | iteT _ _ ih => simp only [Code.all, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => simp only [Code.all, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => exact (ih₂ hc).trans (ih₁ hc)
  | call e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih hc
  | frame e₁ _ e₂ ih =>
    simp only [Code.all, Bool.and_eq_true] at hc
    exact (pop_dit e₂).trans ((ih hc.1.2).trans (push_dit e₁))

/-- `Q`, from `Q` given the entry's PSTATE.DIT, for code that never writes it. -/
theorem WP.of_dit {c : Prog isa} (hc : c.all (fun i => !i.writesDit) = true) {s : State} {Q : State → Prop}
    (h : WP isa c s fun t => t.dit = s.dit → Q t) : WP isa c s Q :=
  let ⟨t, s', e, q⟩ := h
  ⟨t, s', e, q (Exec.dit hc e)⟩

/-- `WP`, and the mode kept, for code that never writes it. -/
theorem WP.dit {c : Prog isa} (hc : c.all (fun i => !i.writesDit) = true) {s : State} {Q : State → Prop}
    (h : WP isa c s Q) : WP isa c s fun t => Q t ∧ t.dit = s.dit :=
  let ⟨t, s', e, q⟩ := h
  ⟨t, s', e, q, Exec.dit hc e⟩

/-- Two runs of `c` along the same trace from the same PSTATE.DIT leave the
same PSTATE.DIT. -/
def DitDet (c : Prog isa) : Prop :=
  ∀ s₁ s₂ t s₁' s₂', Exec isa c s₁ t s₁' → Exec isa c s₂ t s₂' → s₁.dit = s₂.dit → s₁'.dit = s₂'.dit

/-- Code that never writes PSTATE.DIT (the kernel checks `hc` by evaluating the code). -/
theorem DitDet.of_noWrite {c : Prog isa} (hc : c.all (fun i => !i.writesDit) = true) : DitDet c :=
  fun _ _ _ _ _ e₁ e₂ hd => by rw [Exec.dit hc e₁, Exec.dit hc e₂, hd]

end VG.AArch64
