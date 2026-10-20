module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Terms

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def zeroSums : Nat → Sums := fun _ => ⟨0,0,0⟩
def clear : List Instr := [.vop (.movi0 .v21), .vop (.movi0 .v22), .vop (.movi0 .v23)]

theorem zeroLanes : Lanes 0 (fun _ => 0) := by
  intro e he
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem clear_ok {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', VChg [.v21, .v22, .v23] s s' → Accum s' zeroSums → WP isa (.block rest) s' Q) :
    WP isa (.block (clear ++ rest)) s Q := by
  simp only [clear, List.cons_append, List.nil_append]
  refine wp_vop (d := .v21) rfl fun s₁ h₁ => wp_vop (d := .v22) rfl fun s₂ h₂ =>
    wp_vop (d := .v23) rfl fun s₃ h₃ => ?_
  refine k s₃ ((h₁.chg.trans h₂.chg).trans h₃.chg).mono ⟨?_,?_,?_⟩
  · rw [h₃.get .v21, h₂.get .v21, h₁.v]; exact zeroLanes
  · rw [h₃.get .v22, h₂.v]; exact zeroLanes
  · rw [h₃.v]; exact zeroLanes

theorem sumTerms_bound (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {a : Nat → Sums} {n : Nat} (ha : ∀ e < 4, (a e).Bounded n)
    (hF : ∀ fg ∈ terms, ∀ e < 8, F fg e < 3329)
    (hG : ∀ fg ∈ terms, ∀ e < 8, G fg e < 3329) :
    ∀ e < 4, (sumTerms terms F G a e).Bounded (n+terms.length) := by
  induction terms generalizing a n with
  | nil => simpa only [sumTerms, List.foldl_nil, List.length_nil, Nat.add_zero] using ha
  | cons fg terms ih =>
    have hb : ∀ e < 4, (advance a (F fg) (G fg) e).Bounded (n+1) := fun e he =>
      (ha e he).next (hF fg (by simp) _ (by omega)) (hF fg (by simp) _ (by omega))
        (hG fg (by simp) _ (by omega)) (hG fg (by simp) _ (by omega))
    have hr := ih hb (fun fg hf => hF fg (by simp [hf])) (fun fg hf => hG fg (by simp [hf]))
    simpa only [sumTerms, List.foldl_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 terms.length] using hr

end VG.Proof.MlKem.AArch64.Dot
