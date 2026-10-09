import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem run_append (xs ys : List Op) (w : Poly) : run (xs++ys) w=run ys (run xs w) :=
  List.foldl_append

theorem run_layer (len : Nat) (w : Poly) : run (layerSchedule len) w=nttInvLayer w len := by
  unfold run layerSchedule nttInvLayer layerN blockN
  rw [List.foldl_flatMap]
  congr 1
  funext p g
  rw [List.foldl_map, List.range'_eq_map_range, List.foldl_map]
  rfl

theorem run_layers (lens : List Nat) (w : Poly) :
    run (lens.flatMap layerSchedule) w=lens.foldl nttInvLayer w := by
  induction lens generalizing w with
  | nil => rfl
  | cons len lens ih =>
    rw [List.flatMap_cons, run_append, run_layer, List.foldl_cons, ih]

theorem standard_inverse (w : Poly) :
    (run (standardLocal++standardStrided) w).map (· * 8347681)=nttInv w := by
  rw [standardLocal,standardStrided,← List.flatMap_append,run_layers,nttInv_eq_layers]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
