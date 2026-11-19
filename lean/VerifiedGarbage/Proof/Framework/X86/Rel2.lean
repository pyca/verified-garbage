module

public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# Relating two runs from given states (x86, 32-bit)

Where the taint analysis cannot follow code (a frame it has no rule for, a
branch on a value it does not know to be public), two runs are related piece
by piece (`RelCT`) from the two states they start in (`Eq2`): a piece the
analysis checks from registers the correctness proofs pin to the same values
in both runs (`rel_taint`, `rel_taintSse`), or from a taint the states agree
on (`rel_checkT`, and `rel_check`, which also gives what the final states
agree on); then the next piece, from the states the correctness proofs
describe (`rel_seq`, `rel_seqR`, `rel_then`); a branch both runs take the
same way (`rel_ite`, `rel_iteR`); a loop that both leave after the same
number of turns (`rel_loop`).
-/

@[expose] public section

namespace VG.X86

open VG

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.X86.taint.check (τr rs) c h).isSome = true) : RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.X86.taint) _ (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact agree_regs hr) hc

/-- The same, for code with SSE instructions. -/
theorem rel_taintSse {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.X86.sseTaint.check (τr rs) c h).isSome = true) : RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.X86.sseTaint) _ (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact agree_regs hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT :=
  RelCT.nil fun _ _ _ => trivial

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `rel_seq`, with what the first piece's runs leave related (`R`), and
any relation of the final states. -/
theorem rel_seqR {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {R Q : State → State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ R) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, R τ₁ τ₂ → F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq (R := fun a b => R a b ∧ F₁ a ∧ F₂ b) (h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2.1 hp.2.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks from a taint `τ` the two states agree on:
the final states agree on any `m` that says no more than the final taint. -/
theorem rel_check {c : Prog isa} {σ₁ σ₂ : State} {τ : Taint.T} (m : Taint.T) (ha : Taint.Agree τ σ₁ σ₂)
    (hc : ∃ h, (VG.X86.taint.check τ c h).map (VG.X86.taint.le m) = some true) :
    RelCT isa (Eq2 σ₁ σ₂) c (Taint.Agree m) := by
  obtain ⟨h, hc⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨τ', hc', hle⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨ht, hag⟩ := VG.Taint.check_sound (A := VG.X86.taint) hc' ha e₁ e₂
  exact ⟨ht, VG.X86.taint.le_sound hle hag⟩

/-- Code the taint analysis checks from a taint the two states agree on. -/
theorem rel_checkT {c : Prog isa} {σ₁ σ₂ : State} {τ : Taint.T} (ha : Taint.Agree τ σ₁ σ₂)
    (hc : ∃ h, (VG.X86.taint.check τ c h).isSome = true) : RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.X86.taint) _ (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ha) hc

/-- Then: the next piece, from states related as the first piece's runs leave them. -/
theorem rel_then {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {R Q : State → State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ R) (h₂ : ∀ τ₁ τ₂, R τ₁ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq h₁ ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- `rel_ite`, for any relation of the final states. -/
theorem rel_iteR {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} {Q : State → State → Prop}
    (e₁ : isa.eval c σ₁ = some b) (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t Q)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e Q) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) Q := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- A loop both runs leave after the same number of turns: each run keeps an
invariant indexed by the turns left `n`, loops back while `1 < n`, and the
bodies' runs leak the same. -/
theorem rel_loop {body : Prog isa} {c : Cond} (I₁ I₂ : Nat → State → Prop)
    (hb : ∀ n u v, I₁ n u → I₂ n v → RelCT isa (Eq2 u v) body TT)
    (h₁ : ∀ n u, I₁ n u → WP isa body u fun u' => isa.eval c u' = some (decide (1 < n)) ∧ (1 < n → I₁ (n - 1) u'))
    (h₂ : ∀ n v, I₂ n v → WP isa body v fun v' => isa.eval c v' = some (decide (1 < n)) ∧ (1 < n → I₂ (n - 1) v'))
    {n : Nat} {σ₁ σ₂ : State} (i₁ : I₁ n σ₁) (i₂ : I₂ n σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.loop body c) TT := by
  refine (RelCT.loop (Q := TT) (fun k u v => I₁ k u ∧ I₂ k v) (fun k => ?_) n).mono
    (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨i₁, i₂⟩) fun _ _ h => h
  intro u v t₁ t₂ u' v' hp e₁ e₂
  obtain ⟨ht, -⟩ := hb k u v hp.1 hp.2 u v t₁ t₂ u' v' ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨_, w₁, f₁, c₁, n₁⟩ := h₁ k u hp.1
  obtain ⟨_, w₂, f₂, c₂, n₂⟩ := h₂ k v hp.2
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  refine ⟨ht, by rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  rw [c₁] at hc
  have hk : 1 < k := by simpa using hc
  exact ⟨k - 1, by omega, n₁ hk, n₂ hk⟩

end VG.X86
