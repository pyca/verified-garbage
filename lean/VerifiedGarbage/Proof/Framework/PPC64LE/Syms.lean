module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# PPC64LE: the addresses of statics never change

As on ARMv7 (`Proof/Framework/Arm/Syms.lean`): no instruction, call, return
or frame changes `State.syms`, the addresses of the statics the code names
(`adrSym`), so neither does a run (`Exec.syms`): `WP.mono_syms` lets a proof
use that the state after some code names the same addresses as before it.
-/

@[expose] public section

namespace VG.PPC64LE

theorem write_syms (s : State) (r : Reg) (v : BitVec 64) : (s.write r v).syms = s.syms := rfl

/-- `adrSym` puts the static's address in `d`, and the next unknown value in
the link register. -/
theorem exec_adrSym {s : State} {d : Reg} {name : String} (hd : d ≠ .r0) :
    exec (.adrSym d name) s =
      some { s.write d (s.syms name) with lr := s.unknowns 0, unknowns := fun n => s.unknowns (n + 1) } := by
  simp only [exec, ne_eq, hd, not_false_eq_true, ↓reduceIte]

theorem exec_syms {i : Instr} {s s' : State} (h : exec i s = some s') : s'.syms = s.syms := by
  cases i <;> simp only [exec, State.store, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      reduceCtorEq] at h <;> (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, rfl⟩ := h; rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl)
    | (obtain ⟨_, _, h⟩ := h; split at h <;> [(cases h; rfl); cases h])
    | cases h

theorem push_syms {i : Instr} {s s' : State} (h : push i s = some s') : s'.syms = s.syms := by
  cases i <;> simp only [push, reduceCtorEq] at h <;> (repeat' split at h) <;>
    first | (cases h; rfl) | cases h

theorem pop_syms {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') : s'.syms = s₂.syms := by
  cases j <;> simp only [pop, reduceCtorEq] at h <;> (repeat' split at h) <;>
    first | (cases h; rfl) | cases h

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
  | icall hi => nomatch hi
  | icallNext hi => nomatch hi
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

end VG.PPC64LE
