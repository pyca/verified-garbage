import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Relating runs with fewer writable regions (x86-64)

`rel_narrow`: two runs of code that writes only some of its writable
regions are related as the runs from their states with the others moved to
the regions they read only (`Exec.widen`, `Exec.det`). A taint analysis that
knows the writable regions by their index (`Taint.T.lens`, `bases`) can then
check code shared by functions whose other writable regions differ.
-/

namespace VG.X86_64

/-- Two runs, as the runs from their states with the writable regions `ex`
moved to those they read only, and only the writable regions `w` left: the
code runs the same from both (`Exec.widen`, `Exec.det`). -/
theorem rel_narrow {P Q : State → State → Prop} {c : Prog isa} (ex w : List Region)
    (h : RelCT isa (fun σ₁ σ₂ => ∃ s₁ s₂, P s₁ s₂ ∧ σ₁ = s₁.withRegions (s₁.rd ++ ex) w ∧
      σ₂ = s₂.withRegions (s₂.rd ++ ex) w) c Q)
    (hP : ∀ s₁ s₂, P s₁ s₂ → (Covers (ex ++ w) s₁.wr ∧ Covers w s₁.wr ∧
        ∃ t s', Exec isa c (s₁.withRegions (s₁.rd ++ ex) w) t s') ∧
      (Covers (ex ++ w) s₂.wr ∧ Covers w s₂.wr ∧ ∃ t s', Exec isa c (s₂.withRegions (s₂.rd ++ ex) w) t s')) :
    RelCT isa P c fun s₁' s₂' => ∃ σ₁' σ₂', Q σ₁' σ₂' ∧
      (σ₁'.gpr = s₁'.gpr ∧ σ₁'.mem = s₁'.mem ∧ Covers (σ₁'.rd ++ σ₁'.wr) (s₁'.rd ++ s₁'.wr)) ∧
      (σ₂'.gpr = s₂'.gpr ∧ σ₂'.mem = s₂'.mem ∧ Covers (σ₂'.rd ++ σ₂'.wr) (s₂'.rd ++ s₂'.wr)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨⟨c₁, w₁, u₁, σ₁', n₁⟩, ⟨c₂, w₂, u₂, σ₂', n₂⟩⟩ := hP _ _ hp
  have widen : ∀ {s σ' : State} {u : List Leak}, Covers (ex ++ w) s.wr → Covers w s.wr →
      Exec isa c (s.withRegions (s.rd ++ ex) w) u σ' →
      Exec isa c s u (σ'.withRegions s.rd s.wr) ∧ Covers (σ'.rd ++ σ'.wr) (s.rd ++ s.wr) := fun {s σ' u} hc hw n => by
    have m := Exec.widen n (rd := s.rd) (wr := s.wr)
      (by simp only [State.withRegions_rd, State.withRegions_wr, List.append_assoc]
          exact Covers.append (Covers.refl _) hc)
      (by simpa only [State.withRegions_wr] using hw)
    rw [State.withRegions_withRegions, State.withRegions_self] at m
    obtain ⟨hrd, hwr⟩ := Exec.rdwr n
    refine ⟨m, ?_⟩
    rw [hrd, hwr]
    simp only [State.withRegions_rd, State.withRegions_wr, List.append_assoc]
    exact Covers.append (Covers.refl _) hc
  obtain ⟨m₁, v₁⟩ := widen c₁ w₁ n₁
  obtain ⟨m₂, v₂⟩ := widen c₂ w₂ n₂
  obtain ⟨rfl, rfl⟩ := Exec.det e₁ m₁
  obtain ⟨rfl, rfl⟩ := Exec.det e₂ m₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ n₁ n₂
  exact ⟨ht, σ₁', σ₂', hq, ⟨rfl, rfl, v₁⟩, ⟨rfl, rfl, v₂⟩⟩

end VG.X86_64
