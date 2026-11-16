module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# PPC64LE taint tracking with the addresses of statics

As on ARMv7 (`Proof/Framework/Arm/TaintSym.lean`): `taint`, but the
addresses of the statics named in `L` are public (as a contract with those
tables of constants says: `Abi.withConsts`), so the register `adrSym` puts
one in is public, and the code may address the table from it
(`taintSym L`). The analysis sees such an `adrSym d n` as `li d, 0`
(`Instr.symLi`), a public constant, which writes `d` and, of what the
analysis tracks, nothing else, as `adrSym` does (it also writes the link
register, which is not tracked): both runs give `d` the static's address, the
same in both. No instruction changes the addresses (`exec_syms`).
-/

@[expose] public section

namespace VG.PPC64LE

/-- An instruction as `taintSym L` analyses it: `adrSym d n` of a static of
`L` as `li d, 0`, a public constant; the others as they are. -/
def Instr.symLi (L : List String) : Instr → Instr
  | .adrSym d n => if n ∈ L then .li d 0 else .adrSym d n
  | i => i

namespace Taint

/-- `Agree`, and the statics of `L` at the same addresses. -/
def AgreeS (L : List String) (τ : T) (s₁ s₂ : State) : Prop :=
  Agree τ s₁ s₂ ∧ ∀ n ∈ L, s₁.syms n = s₂.syms n

/-- `step`, with the address of a static of `L` public. -/
def stepS (L : List String) (τ : T) (i : Instr) : Option T := step τ (i.symLi L)

theorem stepS_sound {L : List String} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeS L τ s₁ s₂) (hs : stepS L τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ AgreeS L τ' s₁' s₂' := by
  have hsy : ∀ n ∈ L, s₁'.syms n = s₂'.syms n := fun n hn => by
    rw [exec_syms e₁, exec_syms e₂]; exact ha.2 n hn
  unfold stepS at hs
  by_cases hl : ∃ d n, i = .adrSym d n ∧ n ∈ L
  · obtain ⟨d, n, rfl, hn⟩ := hl
    simp only [Instr.symLi, hn, ↓reduceIte, step, Option.some.injEq] at hs
    subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    refine ⟨rfl, ⟨ha.1.1, fun r hr => ?_⟩, hsy⟩
    have w := (ha.1.write d (v₁ := s₁.syms n) (v₂ := s₂.syms n) (p := true) fun _ => ha.2 n hn).2 r hr
    exact w
  · have e : i.symLi L = i := by
      cases i <;> simp only [Instr.symLi]
      rename_i d n
      exact ite_eq_right_of_eq_false _ _ (eq_false fun hn => hl ⟨d, n, rfl, hn⟩)
    rw [e] at hs
    exact ⟨(step_sound ha.1 hs e₁ e₂).1, (step_sound ha.1 hs e₁ e₂).2, hsy⟩

/-- `stepS`, as a function of the instruction first: `step` on every
instruction but `adrSym`, which is public for a static of `L` and is not
analysed otherwise. -/
def stepSFn : Instr → List String → T → Option T
  | .adrSym d n => fun L τ => if n ∈ L then some (set τ d true) else none
  | i => fun _ τ => step τ i

theorem stepSFn_eq (L : List String) (τ : T) (i : Instr) : stepSFn i L τ = stepS L τ i := by
  cases i <;> try rfl
  simp only [stepSFn, stepS, Instr.symLi]
  split <;> rfl

/-- `stepSFn`, with its cases closed (`inline_match%`). -/
def stepSFnK : Instr → List String → T → Option T := inline_match% stepSFn step

theorem stepSFnK_eq (i : Instr) : stepSFnK i = stepSFn i := by cases i <;> rfl

/-- `stepS`, giving a set that is evaluated (see `stepK`). -/
def stepSK (L : List String) (τ : T) (i : Instr) : Option T :=
  match stepSFnK i L τ with
  | some τ' => τ'.force some
  | none => none

theorem stepSK_eq (L : List String) : stepSK L = stepS L := by
  funext τ i
  rw [stepSK, stepSFnK_eq, stepSFn_eq]
  cases stepS L τ i <;> rfl

end Taint

/-- Taint tracking for PPC64LE code that addresses the statics `L`, whose
addresses are public. -/
def taintSym (L : List String) : VG.Taint isa where
  T := Taint.T
  Agree := Taint.AgreeS L
  step := Taint.stepSK L
  step_sound h hs := Taint.stepS_sound h (Taint.stepSK_eq L ▸ hs)
  condPub := taint.condPub
  cond_sound h := taint.cond_sound h.1
  meet := taint.meet
  meet_left h := ⟨taint.meet_left h.1, h.2⟩
  meet_right h := ⟨taint.meet_right h.1, h.2⟩
  le := taint.le
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

/-- `taintSym L`'s step is `Taint.stepS L`'s (`stepSK_eq`). -/
theorem taintSym_step (L : List String) (τ : Taint.T) (i : Instr) :
    (taintSym L).step τ i = Taint.stepS L τ i :=
  congrFun (congrFun (Taint.stepSK_eq L) τ) i

end VG.PPC64LE
