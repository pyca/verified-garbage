import VerifiedGarbage.Proof.Framework.X86.Syms

/-!
# Constant-time analysis of x86 static-table frames

A symbol address is public only when the contract lists it as public.
The saved instruction pointer and the ADD flags are conservatively secret.
The four-byte frame uses the existing checked push/pop analysis.
-/
namespace VG.X86.Taint

/-- Forget a register's region-base identity and flags; set its publicity. -/
def changed (τ : T) (d : Reg) (p : Bool) : T :=
  { τ with regs := set τ d p, flags := false, bases := kill τ d }

/-- Changing one non-stack register, flags, and untracked state. -/
theorem Agree.changed {τ : T} {s₁ s₂ t₁ t₂ : State} (h : Agree τ s₁ s₂)
    {d : Reg} (hd : d ≠ .esp) {p : Bool} (hv : p = true → t₁.gpr d = t₂.gpr d)
    (g₁ : ∀ r, r ≠ d → t₁.gpr r = s₁.gpr r)
    (g₂ : ∀ r, r ≠ d → t₂.gpr r = s₂.gpr r)
    (m₁ : t₁.mem = s₁.mem) (m₂ : t₂.mem = s₂.mem)
    (w₁ : t₁.wr = s₁.wr) (w₂ : t₂.wr = s₂.wr) : Agree (changed τ d p) t₁ t₂ := by
  refine h.keep ⟨?_, fun hf => by cases hf⟩ rfl rfl rfl rfl rfl w₁ w₂ m₁ m₂
    (g₁ _ hd.symm) (g₂ _ hd.symm) (kill_bases h.wf₁ w₁ g₁) (kill_bases h.wf₂ w₂ g₂)
  intro r hr
  change r ∈ set τ d p at hr
  by_cases hp : p = true
  · simp only [set, hp, ↓reduceIte, RegSet.mem_insert] at hr
    rcases hr with rfl | hr
    · exact hv hp
    · by_cases he : r = d
      · subst he; exact hv hp
      · rw [g₁ r he, g₂ r he]; exact h.rf.1 r hr
  · simp only [set, hp, Bool.false_eq_true, ↓reduceIte, RegSet.mem_erase] at hr
    rw [g₁ r hr.1, g₂ r hr.1]; exact h.rf.1 r hr.2

/-- Public symbol addresses supplement the scalar/SSE agreement relation. -/
def AgreeS (L : List String) (τ : T) (s₁ s₂ : State) : Prop :=
  Agree τ s₁ s₂ ∧ ∀ n ∈ L, s₁.syms n = s₂.syms n

/-- Analyze a static-address frame using a secret saved word. -/
def pushSym (L : List String) (τ : T) : Instr → Option T
  | .symPush d n =>
    if d ≠ .esp ∧ n ∈ L then
      (pushStep (changed τ d false) (.push [d])).map fun t => changed t d true
    else none
  | i => pushStep τ i

/-- A static-address push is a secret-word push followed by a public
register write, with the same writable frame. -/
theorem pushSym_sound {L : List String} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeS L τ s₁ s₂) (hs : pushSym L τ i = some τ')
    (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂') :
    isa.addrs i s₁ = isa.addrs i s₂ ∧ AgreeS L τ' s₁' s₂' := by
  have hsy : ∀ n ∈ L, s₁'.syms n = s₂'.syms n := fun n hn => by
    rw [push_syms e₁, push_syms e₂]; exact ha.2 n hn
  cases i with
  | symPush d name =>
    simp only [pushSym] at hs
    split at hs <;> [rename_i hc; cases hs]
    obtain ⟨hd, hl⟩ := hc
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hs
    let a₁ := s₁.setReg d (s₁.unknowns 0)
    let a₂ := s₂.setReg d (s₂.unknowns 0)
    have ha' : Agree (changed τ d false) a₁ a₂ :=
      ha.1.changed hd (fun h => by cases h) (fun _ h => setReg_ne h) (fun _ h => setReg_ne h)
        rfl rfl rfl rfl
    have ea₁ : a₁.gpr .esp = s₁.gpr .esp := setReg_ne hd.symm
    have ea₂ : a₂.gpr .esp = s₂.gpr .esp := setReg_ne hd.symm
    simp only [isa, X86.push] at e₁ e₂
    split at e₁ <;> [rename_i hc₁; cases e₁]
    split at e₂ <;> [rename_i hc₂; cases e₂]
    cases e₁; cases e₂
    have ep₁ : isa.push (.push [d]) a₁ = some (pushState a₁ [d]) := by
      simp only [isa, X86.push, List.length_singleton, Nat.mul_one, ea₁]
      rw [ite_eq_left (by simpa using And.intro hd.symm hc₁.2)]
      simp only [pushState, belowSp, ea₁, List.length_singleton, Nat.mul_one]
    have ep₂ : isa.push (.push [d]) a₂ = some (pushState a₂ [d]) := by
      simp only [isa, X86.push, List.length_singleton, Nat.mul_one, ea₂]
      rw [ite_eq_left (by simpa using And.intro hd.symm hc₂.2)]
      simp only [pushState, belowSp, ea₂, List.length_singleton, Nat.mul_one]
    obtain ⟨_, hp⟩ := push_sound ha' ht ep₁ ep₂
    have hsp : s₁.gpr .esp = s₂.gpr .esp := by
      simp only [pushStep] at ht
      split at ht <;> [rename_i hok; cases ht]
      simp only [Bool.and_eq_true] at hok
      have he := ha'.reg hok.1.1
      exact ea₁.symm.trans (he.trans ea₂)
    refine ⟨by simp only [addrs, hsp], ?_, hsy⟩
    apply hp.changed hd
    · intro _
      simpa only [RegUpd.gpr_setReg_self] using ha.2 name hl
    · intro r hr
      simp only [pushRegs, a₁, RegUpd.gpr_setReg,
        RegUpd.gpr_arithFlags, hr, hd.symm, ↓reduceIte]
    · intro r hr
      simp only [pushRegs, a₂, RegUpd.gpr_setReg,
        RegUpd.gpr_arithFlags, hr, hd.symm, ↓reduceIte]
    · simp only [pushRegs, a₁, State.setReg, hd.symm, ↓reduceIte]
    · simp only [pushRegs, a₂, State.setReg, hd.symm, ↓reduceIte]
    · simp only [List.length_singleton, Nat.mul_one, belowSp, ea₁]; rfl
    · simp only [List.length_singleton, Nat.mul_one, belowSp, ea₂]; rfl
  | _ =>
    simp only [pushSym] at hs
    obtain ⟨a, b⟩ := push_sound ha.1 hs e₁ e₂
    exact ⟨a, b, hsy⟩

end VG.X86.Taint

namespace VG.X86

/-- Scalar/SSE analysis with contract-supplied public static addresses. -/
def taintSym (L : List String) : VG.Taint isa where
  T := Taint.T
  Agree := Taint.AgreeS L
  step := sseTaint.step
  step_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := sseTaint.step_sound h.1 hs e₁ e₂
    exact ⟨a, b, fun n hn => by rw [exec_syms e₁, exec_syms e₂]; exact h.2 n hn⟩
  condPub := sseTaint.condPub
  cond_sound h := sseTaint.cond_sound h.1
  meet := sseTaint.meet
  meet_left h := ⟨sseTaint.meet_left h.1, h.2⟩
  meet_right h := ⟨sseTaint.meet_right h.1, h.2⟩
  le := sseTaint.le
  le_sound hle h := ⟨sseTaint.le_sound hle h.1, h.2⟩
  call := sseTaint.call
  call_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := sseTaint.call_sound h.1 hs e₁ e₂
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨a, b, h.2⟩
  ret := sseTaint.ret
  ret_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := sseTaint.ret_sound h.1 hs e₁ e₂
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨a, b, h.2⟩
  push := Taint.pushSym L
  push_sound := Taint.pushSym_sound
  pop := sseTaint.pop
  pop_sound h hs e₁ e₂ := by
    obtain ⟨a, b⟩ := sseTaint.pop_sound h.1 hs e₁ e₂
    exact ⟨a, b, fun n hn => by rw [pop_syms e₁, pop_syms e₂]; exact h.2 n hn⟩

end VG.X86
