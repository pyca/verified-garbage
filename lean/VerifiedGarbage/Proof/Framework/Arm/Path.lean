module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-!
# ARMv7: runs with the same trace use the same unknowns

The trace of a run records each branch it takes, and each instruction
leaks a number of addresses fixed by the instruction, so two runs of code
without indirect calls that leak the same trace take the same path: they
make the same calls and release the same frames, and so use the same
number of the state's unknowns (`Exec.path`). Two runs that start with the
same unknowns therefore end with the same unknowns, which a proof that a
function returns without secret residue needs when what a release leaves
in a frame depends on them.
-/

@[expose] public section

namespace VG.Arm

/-- `c`, and the functions it calls, make no indirect call. -/
def noIcall : Prog isa → Bool
  | .block _ => true
  | .seq a b => noIcall a && noIcall b
  | .ite _ t e => noIcall t && noIcall e
  | .loop b _ => noIcall b
  | .call _ b => noIcall b
  | .frame _ b _ => noIcall b
  | .icall .. => false

theorem exec_unknowns {i : Instr} {s s' : State} (h : exec i s = some s') : s'.unknowns = s.unknowns := by
  cases i <;> simp only [reduceExec, State.load32, State.load8, State.store32, State.store8,
      Option.map_eq_some_iff, reduceCtorEq] at h <;> (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Option.map_some, Option.map_none] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, rfl⟩ := h; rfl)
    | cases h

/-- How many addresses an instruction leaks depends on the instruction alone. -/
theorem addrs_length (i : Instr) (s s' : State) : (addrs i s).length = (addrs i s').length := by
  cases i <;> simp [addrs, words]

theorem push_unknowns {i : Instr} {s s' : State} (h : push i s = some s') : s'.unknowns = s.unknowns := by
  cases i <;> simp only [push, reduceCtorEq] at h <;> (repeat' split at h) <;>
    first | (cases h; rfl) | cases h

/-- Two releases of a frame by the same instruction, from states with the same
unknowns, leave the same unknowns. -/
theorem pop_unknowns {j : Instr} {a₁ b₁ c₁ a₂ b₂ c₂ : State} (h₁ : isa.pop j a₁ b₁ = some c₁)
    (h₂ : isa.pop j a₂ b₂ = some c₂) (hu : b₁.unknowns = b₂.unknowns) : c₁.unknowns = c₂.unknowns := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h₁ h₂ <;> split at h₁ <;> split at h₂ <;>
    simp only [Option.some.injEq, reduceCtorEq] at h₁ h₂ <;> subst h₁ h₂ <;> exact hu

/-- Two releases of a frame by the same instruction leave the same byte at
`x` if it was the same before them, in states with the same stack pointer
and unknowns. -/
theorem pop_mem_congr {j : Instr} {a₁ b₁ c₁ a₂ b₂ c₂ : State} (h₁ : isa.pop j a₁ b₁ = some c₁)
    (h₂ : isa.pop j a₂ b₂ = some c₂) (_hsp : b₁.sp = b₂.sp) (_hu : b₁.unknowns = b₂.unknowns) {x : Addr}
    (hx : b₁.mem x = b₂.mem x) : c₁.mem x = c₂.mem x := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h₁ h₂ <;> split at h₁ <;> split at h₂ <;>
    simp only [Option.some.injEq, reduceCtorEq] at h₁ h₂ <;> subst h₁ h₂ <;> exact hx

theorem execBlock_path : ∀ {is : List Instr} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) →
    t₁.length = t₂.length ∧ (s₁.unknowns = s₂.unknowns → s₁'.unknowns = s₂'.unknowns)
  | [], _, _, _, _, _, _, h₁, h₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, id⟩
  | i :: is, s₁, s₂, s₁', s₂', t₁, t₂, h₁, h₂ => by
    simp only [execBlock] at h₁ h₂
    split at h₁
    · cases h₁
    · rename_i u₁ e₁
      split at h₂
      · cases h₂
      · rename_i u₂ e₂
        obtain ⟨⟨v₁, r₁⟩, k₁, q₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨⟨v₂, r₂⟩, k₂, q₂⟩ := Option.map_eq_some_iff.mp h₂
        cases q₁; cases q₂
        obtain ⟨hl, hu⟩ := execBlock_path k₁ k₂
        refine ⟨?_, fun h => hu ?_⟩
        · simp only [List.length_append, List.length_map, hl, addrs_length i s₁ s₂]
        · rw [exec_unknowns e₁, exec_unknowns e₂, h]

/-- Two runs of code without indirect calls from states with the same
unknowns, whose traces agree up to what follows them, have the same trace
and end with the same unknowns. -/
theorem Exec.path {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    noIcall c = true → ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak}, Exec isa c s₂ t₂ s₂' →
      t₁ ++ r₁ = t₂ ++ r₂ → s₁.unknowns = s₂.unknowns → t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns := by
  induction e₁ with
  | block h =>
    intro _ s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    cases e₂ with
    | block h' =>
      obtain ⟨hl, hk⟩ := execBlock_path h h'
      exact ⟨(List.append_inj ht hl).1, hk hu⟩
  | seq _ _ ih₁ ih₂ =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | seq a b =>
      simp only [List.append_assoc] at ht
      obtain ⟨rfl, hm⟩ := ih₁ hc.1 a ht hu
      obtain ⟨rfl, he⟩ := ih₂ hc.2 b (List.append_cancel_left ht) hm
      exact ⟨rfl, he⟩
  | iteT _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ b =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih hc.1 b ht hu
      exact ⟨rfl, he⟩
    | iteF _ b => simp at ht
  | iteF _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ b => simp at ht
    | iteF _ b =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih hc.2 b ht hu
      exact ⟨rfl, he⟩
  | loopExit _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | loopExit b _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨rfl, he⟩ := ih hc b ht hu
      exact ⟨rfl, he⟩
    | loopNext b _ _ =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, -⟩ := ih hc b ht hu
      simp at ht
  | loopNext _ _ _ ih₁ ih₂ =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    cases e₂ with
    | loopExit b _ =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, -⟩ := ih₁ hc b ht hu
      simp at ht
    | loopNext b _ l =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, hm⟩ := ih₁ hc b ht hu
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih₂ hc l ht hm
      exact ⟨rfl, he⟩
  | call k _ q ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | call k' b q' =>
      simp only [isa, call, Option.some.injEq] at k k'
      simp only [isa, ret] at q q'
      split at q <;> [cases q; cases q]
      split at q' <;> [cases q'; cases q']
      subst k k'
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht ⊢
      exact ih hc b ht (by simp only [hu])
  | frame p _ q ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | frame p' b q' =>
      simp only [List.append_assoc] at ht
      obtain ⟨ha, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact addrs_length _ _ _)
      obtain ⟨rfl, hm⟩ := ih hc b ht (by
        rw [show isa.push = push from rfl] at p p'
        rw [push_unknowns p, push_unknowns p', hu])
      have ht' := List.append_cancel_left ht
      obtain ⟨hb, -⟩ := List.append_inj ht' (by simp only [List.length_map]; exact addrs_length _ _ _)
      rw [ha, hb]
      exact ⟨rfl, pop_unknowns q q' hm⟩
  | icall => intro hc; simp [noIcall] at hc
  | icallNext => intro hc; simp [noIcall] at hc

end VG.Arm
