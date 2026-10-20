module
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo

/-! # Bounded searches may stop early on a public predicate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

theorem two_bounded_loop {α : Type} {Φ : α → Nat → State → Prop} {Ψ : α → State → Prop}
    (bound : α → Nat) (again : α → Nat → Bool) {body : Prog isa} {cond : Cond}
    (hct : RelCT isa (Two fun (p : α × Nat) s => p.2 < bound p.1 ∧ Φ p.1 p.2 s) body (fun _ _ => True))
    (hw : ∀ p i s, i < bound p → Φ p i s → WP isa body s fun t =>
      isa.eval cond t = some (again p i) ∧
      (again p i = true → i + 1 < bound p ∧ Φ p (i + 1) t) ∧
      (again p i = false → Ψ p t)) :
    RelCT isa (Two fun (p : α × Nat) s => p.2 < bound p.1 ∧ Φ p.1 p.2 s)
      (.loop body cond) (Two Ψ) := by
  have step (n : Nat) := two_post
    (Φ := fun (p : α × Nat) s => n = bound p.1 - p.2 ∧ p.2 < bound p.1 ∧ Φ p.1 p.2 s)
    (Ψ := fun p t => n = bound p.1 - p.2 ∧ p.2 < bound p.1 ∧ isa.eval cond t = some (again p.1 p.2) ∧
      (again p.1 p.2 = true → p.2 + 1 < bound p.1 ∧ Φ p.1 (p.2 + 1) t) ∧
      (again p.1 p.2 = false → Ψ p.1 t))
    (hct.mono (fun _ _ => two_mono (fun _ _ h => h.2)) (fun _ _ h => h))
    (fun p s h => WP.mono (hw p.1 p.2 s h.2.1 h.2.2) fun _ h' => ⟨h.1, h.2.1, h'⟩)
  have loop := RelCT.loop (M := isa) (body := body) (c := cond) (Q := Two Ψ)
    (fun n s t => ∃ p i, n = bound p - i ∧ i < bound p ∧ Φ p i s ∧ Φ p i t) (fun n => ?_)
  · intro s t ts tt s' t' ⟨⟨p, i⟩, hs, ht⟩ es et
    exact loop (bound p - i) s t ts tt s' t' ⟨p, i, rfl, hs.1, hs.2, ht.2⟩ es et
  · refine (step n).mono ?_ ?_
    · rintro s t ⟨p, i, hn, hi, hs, ht⟩
      exact ⟨(p, i), ⟨hn, hi, hs⟩, hn, hi, ht⟩
    · rintro s t ⟨⟨p, i⟩, ⟨hn, hi, es, ns, ds⟩, ⟨_, _, et, nt, dt⟩⟩
      refine ⟨es.trans et.symm, ?_, ?_⟩
      · intro stop
        have h : again p i = false := Option.some.inj (es.symm.trans stop)
        exact ⟨p, ds h, dt h⟩
      · intro more
        have h : again p i = true := Option.some.inj (es.symm.trans more)
        obtain ⟨hi', hs⟩ := ns h
        change n = bound p - i at hn
        change i < bound p at hi
        exact ⟨bound p - (i + 1), by omega, p, i + 1, rfl, hi', hs, (nt h).2⟩
end VG.Proof.Dsa.X86.Generation
