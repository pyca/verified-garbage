module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalChecked
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ## From `TraversalSpec.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem run_append (xs ys : List Op) (w : Poly) : run (xs++ys) w=run ys (run xs w) :=
  List.foldl_append

theorem run_layer (len : Nat) (w : Poly) : run (layerSchedule len) w=nttLayer w len := by
  unfold run layerSchedule nttLayer layerN blockN
  rw [List.foldl_flatMap]
  congr 1
  funext p g
  rw [List.foldl_map, List.range'_eq_map_range, List.foldl_map]
  rfl

theorem run_layers (lens : List Nat) (w : Poly) :
    run (lens.flatMap layerSchedule) w=lens.foldl nttLayer w := by
  induction lens generalizing w with
  | nil => rfl
  | cons len lens ih =>
    rw [List.flatMap_cons, run_append, run_layer, List.foldl_cons, ih]

theorem standard_ntt (w : Poly) : run (standardOuter++standardInner) w=ntt w := by
  rw [standardOuter,standardInner,← List.flatMap_append,run_layers,ntt_eq_layers]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Traversal

end

/-! ## From `TraversalCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem outer_run (w : Poly) : run outerSchedule w=run standardOuter w :=
  (Schedule.check_run (fun _ _ h => mask_comm h) outer_checked w).symm

theorem inner_run (w : Poly) : run innerSchedule w=run standardInner w :=
  (Schedule.check_run (fun _ _ h => mask_comm h) inner_checked w).symm

/-- The selected three-layer strided pass followed by five-layer contiguous
passes is exactly the standard forward transform. -/
theorem traversal_ntt (w : Poly) : run innerSchedule (run outerSchedule w)=ntt w := by
  rw [outer_run, inner_run, ← run_append, standard_ntt]

theorem ofInt_zetaNat (k : Nat) : ofInt (zetaNat k : Int)=zetas k := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [VG.Proof.MlDsa.KeyGen.ofInt_val]
  rw [Int.emod_eq_of_lt (by omega) (by have := zetaNat_lt k; change _<8380417 at this; omega)]
  exact congrArg (fun n : Nat => (n : Int)) (zetaNat_eq k)

end VG.Proof.MlDsa.AArch64.Optimized.Traversal

end
