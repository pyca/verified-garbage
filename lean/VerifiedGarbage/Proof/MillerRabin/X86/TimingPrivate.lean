module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Timing composition retains independent secret values for the two runs -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Dsa.X86

/-- The shared geometry is public; each execution retains its own private state. -/
def Two {α : Type} (g : Geometry) (F : α → State → Prop) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ (∃ σ, F σ s) ∧ (∃ σ, F σ t)

theorem private_lift {α : Type} {g : Geometry} {F G : α → State → Prop} {code : Prog isa}
    (trace : RelCT isa (Pair g [.edi]) code (Pair g [.edi]))
    (step : ∀ σ s, F σ s → WP isa code s (G σ)) :
    RelCT isa (Two g F) code (Two g G) := by
  intro s t tr ur u z ⟨H, ⟨σ, S⟩, ⟨ρ, T⟩⟩ E B
  obtain ⟨same, P⟩ := trace _ _ _ _ _ _ H E B
  exact ⟨same, P, ⟨σ, wp_result (step σ s S) E⟩, ⟨ρ, wp_result (step ρ t T) B⟩⟩

theorem private_mono {α : Type} {g : Geometry} {F G : α → State → Prop}
    (imp : ∀ σ s, F σ s → G σ s) {s t : State} (H : Two g F s t) : Two g G s t := by
  obtain ⟨P, ⟨σ, S⟩, ⟨ρ, T⟩⟩ := H
  exact ⟨P, ⟨σ, imp σ s S⟩, ⟨ρ, imp ρ t T⟩⟩

theorem private_count_loop {α : Type} {g : Geometry} {F : Nat → α → State → Prop} {code : Prog isa}
    (step : ∀ q, 0 < q → RelCT isa (Two g (F q)) code fun s t =>
      Two g (F (q - 1)) s t ∧ isa.eval .ne s = some (decide (1 < q)) ∧ isa.eval .ne t = some (decide (1 < q)))
    (q : Nat) (positive : 0 < q) :
    RelCT isa (Two g (F q)) (.loop code .ne) (Two g (F 0)) := by
  have loop := RelCT.loop (M := isa) (body := code) (c := .ne)
    (I := fun q s t => 0 < q ∧ Two g (F q) s t) (Q := Two g (F 0)) ?_ q
  · exact loop.mono (fun _ _ H => ⟨positive, H⟩) (fun _ _ H => H)
  · intro n s t tr ur u z ⟨pos, H⟩ E B
    obtain ⟨same, T, Eu, Ez⟩ := step n pos _ _ _ _ _ _ H E B
    refine ⟨same, Eu.trans Ez.symm, ?_, ?_⟩
    · intro exit
      have small : ¬ 1 < n := by rw [Eu] at exit; simpa using exit
      have eq : n - 1 = 0 := by omega
      rw [eq] at T
      exact T
    · intro next
      have more : 1 < n := by rw [Eu] at next; simpa using next
      exact ⟨n - 1, by omega, by omega, T⟩

end VG.Proof.MillerRabin.X86
