import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# AArch64 taint tracking with the addresses of statics

`taint`, but the addresses of the statics named in `L` are public (as a
contract with those tables of constants says: `Abi.withConsts`), so the
register `adrSym` puts one in is public, and the code may address the table
from it (`taintS L`). No instruction changes the addresses (`exec_syms`).
-/

namespace VG.AArch64

/-- The register an instruction puts the address of a static in, and the
static's name. -/
def Instr.sym : Instr → Option (Reg × String)
  | .adrSym d n => some (d, n)
  | _ => none

theorem Instr.sym_eq {i : Instr} {d : Reg} {n : String} (h : i.sym = some (d, n)) :
    i = .adrSym d n := by
  cases i <;> simp only [Instr.sym, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

namespace Taint

/-- `Agree`, and the statics of `L` at the same addresses. -/
def AgreeS (L : List String) (τ : T) (s₁ s₂ : State) : Prop :=
  Agree τ s₁ s₂ ∧ ∀ n ∈ L, s₁.syms n = s₂.syms n

/-- `step`, with the address of a static of `L` public. -/
def stepS (L : List String) (τ : T) (i : Instr) : Option T :=
  match i.sym with
  | some (d, n) => if n ∈ L then some (set τ d true) else step τ i
  | none => step τ i

theorem stepS_sound {L : List String} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeS L τ s₁ s₂) (hs : stepS L τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ AgreeS L τ' s₁' s₂' := by
  have hsy : ∀ n ∈ L, s₁'.syms n = s₂'.syms n := fun n hn => by
    rw [exec_syms e₁, exec_syms e₂]; exact ha.2 n hn
  unfold stepS at hs
  split at hs
  · rename_i d n hsym
    obtain rfl := Instr.sym_eq hsym
    split at hs
    · rename_i hn
      cases hs
      simp only [exec, Option.some.injEq] at e₁ e₂
      subst e₁ e₂
      exact ⟨rfl, ha.1.write .x d (p := true) fun _ => ha.2 n hn, hsy⟩
    · exact ⟨(step_sound ha.1 hs e₁ e₂).1, (step_sound ha.1 hs e₁ e₂).2, hsy⟩
  · exact ⟨(step_sound ha.1 hs e₁ e₂).1, (step_sound ha.1 hs e₁ e₂).2, hsy⟩

end Taint

/-- Taint tracking for AArch64 code that addresses the statics `L`, whose
addresses are public. -/
def taintS (L : List String) : VG.Taint isa where
  T := Taint.T
  Agree := Taint.AgreeS L
  step := Taint.stepS L
  step_sound := Taint.stepS_sound
  condPub := Taint.condPub
  cond_sound h := Taint.cond_sound h.1
  meet τ₁ τ₂ := τ₁.inter τ₂
  meet_left h := ⟨taint.meet_left h.1, h.2⟩
  meet_right h := ⟨taint.meet_right h.1, h.2⟩
  le τ σ := τ.subset σ
  le_sound hle h := ⟨taint.le_sound hle h.1, h.2⟩
  call := taint.call
  call_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := taint.call_sound h.1 hs e₁ e₂
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨a, b, h.2⟩
  ret := taint.ret
  ret_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := taint.ret_sound h.1 hs e₁ e₂
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨a, b, h.2⟩
  push := taint.push
  push_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := taint.push_sound h.1 hs e₁ e₂
    exact ⟨a, b, fun n hn => by rw [push_syms e₁, push_syms e₂]; exact h.2 n hn⟩
  pop := taint.pop
  pop_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := taint.pop_sound h.1 hs e₁ e₂
    exact ⟨a, b, fun n hn => by rw [pop_syms e₁, pop_syms e₂]; exact h.2 n hn⟩

end VG.AArch64
