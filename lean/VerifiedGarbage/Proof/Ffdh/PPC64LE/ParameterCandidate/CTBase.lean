module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# An FFDH parameter candidate on PPC64LE: relating two runs

Two runs are related by `Two Φ` (`MontCT.lean`): both satisfy `Φ a` for the
same public data `a`. `two_ite` branches on a condition `Φ a` fixes;
`two_loopD` loops while a condition `Φ a` fixes holds, the next iteration's
data a function of `a`, a measure of it decreasing.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE
open VG.Proof.Bignum.PPC64LE (Two two_post)

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨g a, h _ _ h₁, h _ _ h₂, hsp⟩) fun _ _ h => h

theorem two_mono {α : Type} {Φ Φ' : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a s, Φ a s → Φ' a s) (hct : RelCT isa (Two Φ') c Q) : RelCT isa (Two Φ) c Q :=
  two_map id h hct

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩

/-- A branch on a condition `Φ a` decides. -/
theorem two_ite' {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop} (b : α → Bool) (hc : ∀ a s, Φ a s → isa.eval cond s = some (b a))
    (ht : RelCT isa (Two fun a s => Φ a s ∧ b a = true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ b a = false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q :=
  two_ite (fun a _ _ h₁ h₂ => (hc a _ h₁).trans (hc a _ h₂).symm)
    (two_mono (fun a s ⟨h, hb⟩ => ⟨h, by rw [hc a s h] at hb; exact Option.some.inj hb⟩) ht)
    (two_mono (fun a s ⟨h, hb⟩ => ⟨h, by rw [hc a s h] at hb; exact Option.some.inj hb⟩) he)

/-- A loop whose condition `Φ a` decides (`go a`), from data `next a` of
smaller measure when it goes on. -/
theorem two_loopD {α : Type} {Φ Ψ : α → State → Prop} (μ : α → Nat) (next : α → α) (go : α → Bool)
    {body : Prog isa} {cond : isa.Cond}
    (hct : RelCT isa (Two Φ) body fun _ _ => True)
    (hw : ∀ a s, Φ a s → WP isa body s fun s' => isa.eval cond s' = some (go a) ∧
      (go a = false → Ψ a s') ∧ (go a = true → μ (next a) < μ a ∧ Φ (next a) s')) :
    RelCT isa (Two Φ) (.loop body cond) (Two Ψ) := by
  have key := RelCT.loop (M := isa) (body := body) (c := cond) (Q := Two Ψ)
    (fun n s₁ s₂ => ∃ a, n = μ a ∧ Φ a s₁ ∧ Φ a s₂ ∧ s₁.sp = s₂.sp) (fun n => by
      have hp := two_post (Φ := fun a s => n = μ a ∧ Φ a s)
        (Ψ := fun a s' => n = μ a ∧ isa.eval cond s' = some (go a) ∧
          (go a = false → Ψ a s') ∧ (go a = true → μ (next a) < μ a ∧ Φ (next a) s'))
        (two_mono (fun a s h => h.2) hct) fun a s h => WP.mono (hw a s h.2) fun s' h' => ⟨h.1, h'⟩
      refine hp.mono (fun s₁ s₂ ⟨a, hn, h₁, h₂, hsp⟩ => ⟨a, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
      rintro s₁ s₂ ⟨a, ⟨hn, e₁, f₁, g₁⟩, ⟨-, e₂, f₂, g₂⟩, hsp⟩
      refine ⟨by rw [e₁, e₂], fun h => ?_, fun h => ?_⟩
      · have hg : go a = false := by rw [e₁] at h; exact Option.some.inj h
        exact ⟨a, f₁ hg, f₂ hg, hsp⟩
      · have hg : go a = true := by rw [e₁] at h; exact Option.some.inj h
        exact ⟨μ (next a), by rw [hn]; exact (g₁ hg).1, next a, rfl, (g₁ hg).2, (g₂ hg).2, hsp⟩)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  exact key (μ a) _ _ _ _ _ _ ⟨a, rfl, h₁, h₂, hsp⟩ e₁ e₂

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
