module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingPrivate
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Attach each run's functional invariant to a checked public-address trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Dsa.X86

theorem private_attach {α : Type} {g : Geometry} {F G : α → State → Prop} {code : Prog isa}
    (trace : RelCT isa (Two g F) code (VG.X86.Taint.Agree (roundTaint [.edi])))
    (step : ∀ σ s, F σ s → WP isa code s (G σ))
    (context : ∀ σ s, G σ s → Context g s) :
    RelCT isa (Two g F) code (Two g G) := by
  intro s t tr ur u z H E B
  obtain ⟨same, A⟩ := trace _ _ _ _ _ _ H E B
  obtain ⟨_, ⟨σ, S⟩, ⟨ρ, T⟩⟩ := H
  have Gu := wp_result (step σ s S) E
  have Gz := wp_result (step ρ t T) B
  exact ⟨same, ⟨context σ u Gu, context ρ z Gz, A⟩, ⟨σ, Gu⟩, ⟨ρ, Gz⟩⟩

theorem ne_of_zf {s : State} {q : Nat} (positive : 0 < q) (Z : s.zf = some (decide (q = 1))) :
    isa.eval .ne s = some (decide (1 < q)) := by
  change Option.map Bool.not s.zf = _
  rw [Z]
  by_cases eq : q = 1
  · simp [eq]
  · have more : 1 < q := by omega
    simp [eq, more]

theorem private_control {α : Type} {g : Geometry} {F G : α → State → Prop} {code : Prog isa} {q : Nat}
    (trace : RelCT isa (Two g F) code (VG.X86.Taint.Agree (roundTaint [.edi])))
    (step : ∀ σ s, F σ s → WP isa code s fun t => G σ t ∧ t.zf = some (decide (q = 1)))
    (context : ∀ σ s, G σ s → Context g s) (positive : 0 < q) :
    RelCT isa (Two g F) code fun s t => Two g G s t ∧
      isa.eval .ne s = some (decide (1 < q)) ∧ isa.eval .ne t = some (decide (1 < q)) := by
  intro s t tr ur u z H E B
  obtain ⟨same, A⟩ := trace _ _ _ _ _ _ H E B
  obtain ⟨_, ⟨σ, S⟩, ⟨ρ, T⟩⟩ := H
  obtain ⟨Gu, Zu⟩ := wp_result (step σ s S) E
  obtain ⟨Gz, Zz⟩ := wp_result (step ρ t T) B
  refine ⟨same, ⟨⟨context σ u Gu, context ρ z Gz, A⟩, ⟨σ, Gu⟩, ⟨ρ, Gz⟩⟩, ?_, ?_⟩
  · exact ne_of_zf positive Zu
  · exact ne_of_zf positive Zz

end VG.Proof.MillerRabin.X86
