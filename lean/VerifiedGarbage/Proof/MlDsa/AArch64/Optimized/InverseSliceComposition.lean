module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- A slice depends only on coefficients belonging to that slice. -/
theorem run_slice_congr (ops : List Op) (slice : Nat → Nat) (u : Nat)
    (hs : ops.all (supported slice u)=true) (v w : Poly)
    (hvw : ∀ k<n, slice k=u → v[k]! =w[k]!) :
    ∀ k<n, slice k=u → (run ops v)[k]! =(run ops w)[k]! := by
  induction ops generalizing v w with
  | nil => exact hvw
  | cons o ops ih =>
    simp only [List.all_cons,Bool.and_eq_true] at hs
    have ho : 0<o.length ∧ o.index+o.length<n ∧ slice o.index=u ∧ slice (o.index+o.length)=u :=
      of_decide_eq_true hs.1
    apply ih hs.2 (o.apply v) (o.apply w)
    intro k hk hku
    unfold Op.apply
    rw [bflyInv_get v ho.1 ho.2.1 _ hk,bflyInv_get w ho.1 ho.2.1 _ hk,
      hvw o.index (by omega_using [ho]) ho.2.2.1,hvw (o.index+o.length) ho.2.1 ho.2.2.2,hvw k hk hku]

theorem prefix_outside (slices : Nat → List Op) (slice : Nat → Nat) (N : Nat)
    (hs : ∀ u<N, (slices u).all (supported slice u)=true) (w : Poly)
    {k : Nat} (hk : k<n) (hbefore : N≤slice k) :
    (run ((List.range N).flatMap slices) w)[k]! =w[k]! := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,run_append,
      run_outside _ _ N (hs N (by omega_using [])) _ hk (by omega_using [hbefore])]
    exact ih (fun u hu => hs u (by omega_using [hu])) (by omega_using [hbefore])

/-- In a prefix of independent slices, each completed coordinate equals its
own slice evaluated on the original input polynomial. -/
theorem prefix_selected (slices : Nat → List Op) (slice : Nat → Nat) (N : Nat)
    (hs : ∀ u<N, (slices u).all (supported slice u)=true) (w : Poly)
    {k : Nat} (hk : k<n) (hselected : slice k<N) :
    (run ((List.range N).flatMap slices) w)[k]! =(run (slices (slice k)) w)[k]! := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,run_append]
    by_cases he : slice k=N
    · rw [he]
      apply run_slice_congr _ slice N (hs N (by omega_using [])) _ w ?_ k hk he
      intro j hj hju
      exact prefix_outside slices slice N (fun u hu => hs u (by omega_using [hu])) w hj (by omega_using [hju])
    · rw [run_outside _ _ N (hs N (by omega_using [])) _ hk he]
      exact ih (fun u hu => hs u (by omega_using [hu])) (by omega_using [hselected, he])

theorem strided_coordinate (w : Poly) {k : Nat} (hk : k<n) :
    (run stridedSchedule w)[k]! =(run (stridedSlice (k%32/4)) w)[k]! := by
  exact prefix_selected stridedSlice (fun k => k%32/4) 8
    (fun u hu => strided_supported ⟨u,hu⟩) w hk (by omega_using [])

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
