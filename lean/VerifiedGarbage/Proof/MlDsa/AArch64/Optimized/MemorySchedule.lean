import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.Framework.PowLit

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Every operation stays within its selected slice. -/
def supported (slice : Nat → Nat) (u : Nat) (o : Op) : Bool := decide
  (0<o.length ∧ o.index+o.length<n ∧ slice o.index=u ∧ slice (o.index+o.length)=u)

theorem outer_supported : ∀ u : Fin 8,
    (outerSlice u.val).all (supported (fun k => k%32/4) u.val)=true := by decide +kernel

theorem inner_supported : ∀ u : Fin 8,
    (innerSlice u.val).all (supported (fun k => k/32) u.val)=true := by decide +kernel

theorem run_outside (ops : List Op) (slice : Nat → Nat) (u : Nat)
    (hs : ops.all (supported slice u)=true) (w : Poly) {k : Nat} (hk : k<n)
    (ho : slice k≠u) : (run ops w)[k]! = w[k]! := by
  induction ops generalizing w with
  | nil => rfl
  | cons o ops ih =>
    simp only [List.all_cons,Bool.and_eq_true] at hs
    obtain ⟨h,hs⟩ := hs
    have h' : 0<o.length ∧ o.index+o.length<n ∧ slice o.index=u ∧ slice (o.index+o.length)=u :=
      of_decide_eq_true h
    change (run ops (o.apply w))[k]! = _
    rw [ih hs]
    unfold Op.apply
    rw [bfly_get w h'.1 h'.2.1 _ hk]
    have h0 : o.index≠k := fun he => ho (he ▸ h'.2.2.1)
    have h1 : o.index+o.length≠k := fun he => ho (he ▸ h'.2.2.2)
    simp only [Ne.symm h0,Ne.symm h1,ite_false]

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
