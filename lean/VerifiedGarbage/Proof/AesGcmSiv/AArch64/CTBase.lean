import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-GCM-SIV on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2`) piece by piece, as AES-GCM's do
(`Proof.AesGcm.AArch64.rel_seq`): the code between calls by the taint
analysis, from the registers that hold the public arguments in both runs
(`Env`, `rel_env`) and those the pieces pin to the same values; each call
by its callee's proof; and the next piece from the states the correctness
proofs describe.
-/

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_taint)

theorem Env.agree {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) :
    ∀ r ∈ envRegs, τ₁.gpr r = τ₂.gpr r := by
  intro r hr
  simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.x19, E₂.x19]
  · rw [E₁.x20, E₂.x20]
  · rw [E₁.x21, E₂.x21]
  · rw [E₁.x22, E₂.x22]
  · rw [E₁.x23, E₂.x23]
  · rw [E₁.x24, E₂.x24]
  · rw [E₁.x25, E₂.x25]
  · rw [E₁.x26, E₂.x26]

theorem Env.sp_eq {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) : τ₁.sp = τ₂.sp := by
  rw [E₁.sp, E₂.sp]

/-- The registers holding the public arguments, and `rs`. -/
abbrev pubRegs (rs : List Reg) : List Reg := envRegs ++ rs

/-- Code the taint analysis checks, from the registers holding the public
arguments and the registers `rs` the two runs agree on. -/
theorem rel_env {c : Prog isa} {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ rs)) c h).isSome = true) :
    RelCT isa (Eq2 τ₁ τ₂) c TT :=
  rel_taint (envRegs ++ rs) (E₁.sp_eq E₂) (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) hc

/-- Then, towards any relation of the final states. -/
theorem rel_seqQ {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- The last piece, with what correctness says of each run's final state. -/
theorem rel_wpQ {c : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h : RelCT isa (Eq2 σ₁ σ₂) c TT) (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂)
    (hq : ∀ a b, F₁ a → F₂ b → Q a b) : RelCT isa (Eq2 σ₁ σ₂) c Q :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun a b h => hq a b h.2.1 h.2.2

/-- `a; (b; (c; (d; e)))`, related as `(a; (b; (c; d))); e`. -/
theorem RelCT.assoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
  | seq d₁ e₁' =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
  | seq d₂ e₂' =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) e₁')
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) e₂')
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- A loop step in two runs: the condition agrees, and the runs are related
anew while it loops. -/
theorem rel_loop {body : Prog isa} {c : Cond} (I : Nat → State → State → Prop)
    (hstep : ∀ n σ₁ σ₂, I n σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) body fun s₁ s₂ => isa.eval c s₁ = isa.eval c s₂ ∧
      (isa.eval c s₁ = some true → ∃ m < n, I m s₁ s₂))
    (n : Nat) {σ₁ σ₂ : State} (h : I n σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.loop body c) TT := by
  refine (RelCT.loop (Q := TT) I (fun n => ?_) n).mono (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact h)
    fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hc, hi⟩ := hstep n s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, hc, fun _ => trivial, hi⟩

end VG.Proof.AesGcmSiv.AArch64
