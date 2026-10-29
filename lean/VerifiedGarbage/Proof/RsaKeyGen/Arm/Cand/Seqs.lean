module

public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Pieces of sequences (ARMv7)

`seqs (a ++ b)` runs as `seqs a` then `seqs b` (`exec_seqs_app`), so pieces
of each compose (`VP.seqs_app`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys
open VG.Proof.Rsa.Arm.Recover (VP)

theorem exec_seqs_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t : List Leak}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      have e₂' := ih (by simp) e₂
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases e₂' with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

/-- A piece whose stages imply a fact about the public parameters. -/
theorem VP.ofImp {F G : State → State → Prop} {c : Prog isa} {p : Prop} (hp : ∀ σ s, F σ s → p)
    (h : p → VP F c G) : VP F c G :=
  ⟨fun σ s hs => (h (hp σ s hs)).wp σ s hs, fun s₁ s₂ t₁ t₂ s₁' s₂' hs e₁ e₂ =>
    match hs with
    | ⟨σ₁, σ₂, h₁, h₂⟩ => (h (hp _ _ h₁)).ct s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂⟩

/-- Pieces of `seqs a` and `seqs b`: a piece of `seqs (a ++ b)`. -/
theorem VP.seqs_app {F G H : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h₁ : VP F (seqs a) G) (h₂ : VP G (seqs b) H) : VP F (seqs (a ++ b)) H := by
  have h := h₁.seq h₂
  exact ⟨fun σ s hs => (VG.Proof.Rsa.Arm.Keys.wp_seqs_append ha hb).mpr (WP.mono (h₁.wp σ s hs) fun t ht => h₂.wp σ t ht),
    fun _ _ _ _ _ _ hp e₁ e₂ => h.ct _ _ _ _ _ _ hp (exec_seqs_app ha hb e₁) (exec_seqs_app ha hb e₂)⟩

end VG.Proof.RsaKeyGen.Arm.Cand
