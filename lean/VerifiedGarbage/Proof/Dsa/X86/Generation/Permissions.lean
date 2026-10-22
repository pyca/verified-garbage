module

public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.RelCT

/-! Reuse workspace proofs under the generation caller's larger permissions.
The component's own postcondition supplies its precise write frame, including
any stack it uses, so this lifting also applies to calls and allocated frames. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

theorem workspace_wp {code : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (H : WP isa code (s.withRegions rd wr) P)
    (reads : Covers (rd ++ wr) (s.rd ++ s.wr)) (writes : Covers wr s.wr) :
    WP isa code s fun t => ∃ u, P u ∧ t = u.withRegions s.rd s.wr := by
  obtain ⟨trace, u, E, post⟩ := H
  have run := VG.X86.Exec.widen E reads writes
  simp only [State.withRegions_withRegions,
    State.withRegions_self] at run
  exact ⟨trace, _, run, u, post, rfl⟩

theorem workspace_ct {code : Prog isa} {P Q : State → State → Prop}
    (rd wr : State → List Region)
    (reads : ∀ s t, P s t → Covers (rd s ++ wr s) (s.rd ++ s.wr) ∧
      Covers (rd t ++ wr t) (t.rd ++ t.wr))
    (writes : ∀ s t, P s t → Covers (wr s) s.wr ∧ Covers (wr t) t.wr)
    (ready : ∀ s t, P s t → (∃ tr u, Exec isa code (s.withRegions (rd s) (wr s)) tr u) ∧
      (∃ tr v, Exec isa code (t.withRegions (rd t) (wr t)) tr v))
    (timing : ∀ s t, P s t → ∀ tr ur u v,
      Exec isa code (s.withRegions (rd s) (wr s)) tr u →
      Exec isa code (t.withRegions (rd t) (wr t)) ur v → tr = ur)
    (post : ∀ s t tr ur u v, P s t → Exec isa code s tr u → Exec isa code t ur v → Q u v) :
    RelCT isa P code Q := by
  intro s t tr ur u v H E F
  obtain ⟨⟨tr', u', E'⟩, ⟨ur', v', F'⟩⟩ := ready s t H
  have Eu := VG.X86.Exec.widen E' (reads s t H).1 (writes s t H).1
  have Fv := VG.X86.Exec.widen F' (reads s t H).2 (writes s t H).2
  simp only [State.withRegions_withRegions,
    State.withRegions_self] at Eu Fv
  have sameLeft := (Exec.det E Eu).1
  have sameRight := (Exec.det F Fv).1
  exact ⟨sameLeft.trans ((timing s t H _ _ _ _ E' F').trans sameRight.symm), post _ _ _ _ _ _ H E F⟩

end VG.Proof.Dsa.X86.Generation
