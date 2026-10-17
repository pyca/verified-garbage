module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawBodyCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: timing of uniform rejection sampling -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate

private def drawInv (n : Nat) : State → State → Prop :=
  Two fun d s => d.bs.length = n ∧ DrawBefore d s

private theorem draw_step (n : Nat) : RelCT isa (drawInv n) drawBody fun s₁ s₂ =>
    isa.eval .e s₁ = isa.eval .e s₂ ∧ (isa.eval .e s₁ = some false → True) ∧
      (isa.eval .e s₁ = some true → ∃ m < n, drawInv m s₁ s₂) := by
  have hc : RelCT isa (drawInv n) drawBody
      (Two fun d s => d.bs.length = n ∧ DrawAfter d s) :=
    two_post (two_map (fun d : DrawPublic => d) (fun _ _ h => h.2) drawBody_ct)
      (fun d s h => WP.mono (drawBody_after d s h.2) fun _ ht => ⟨h.1, ht⟩)
  refine hc.mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨d, ⟨hsize, h₁⟩, ⟨_, h₂⟩⟩
  by_cases ha : d.p.len ≤ d.bs.length
  · simp only [DrawAfter, ite_eq_left ha] at h₁ h₂
    refine ⟨by simp only [eval, h₁.1.2, h₂.1.2], fun _ => trivial, fun _ => ?_⟩
    let d' : DrawPublic := { d with rp := off d.rp d.p.len, used := d.used + d.p.len, bs := d.bs.drop d.p.len }
    refine ⟨d'.bs.length, ?_, d', ⟨rfl, ⟨h₁.1.1, h₁.2⟩⟩, ⟨rfl, ⟨h₂.1.1, h₂.2⟩⟩⟩
    change (d.bs.drop d.p.len).length < n
    rw [List.length_drop]
    omega_using [ha, hsize, d.p.width_bounds.2.2.1]
  · simp only [DrawAfter, ite_eq_right ha] at h₁ h₂
    refine ⟨by simp only [eval, h₁.1.2, h₂.1.2], fun _ => trivial, ?_⟩
    intro he
    simp only [eval, h₁.1.2, Option.some.injEq, Bool.false_eq_true] at he

theorem drawWitness_ct : RelCT isa (Two DrawBefore) drawWitness fun _ _ => True := by
  rintro s₁ s₂ tr₁ tr₂ t₁ t₂ ⟨d, h₁, h₂⟩ e₁ e₂
  exact RelCT.loop drawInv draw_step d.bs.length s₁ s₂ tr₁ tr₂ t₁ t₂
    ⟨d, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩⟩ e₁ e₂

end VG.Proof.Ffdh.X86_64.ParameterCandidate
