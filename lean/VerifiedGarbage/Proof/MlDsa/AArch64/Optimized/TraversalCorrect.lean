import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalChecked

/-! ## From `TraversalSpec.lean` -/

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

def Op.toButterfly (o : Op) : ButterflyOp := ⟨o.index,o.length,(zetaNat o.rootIndex : Int)⟩

def valid (o : Op) : Bool := decide (0<o.length ∧ o.index+o.length<n)

theorem outer_valid : outerSchedule.all valid=true := by decide +kernel
theorem inner_valid : innerSchedule.all valid=true := by decide +kernel

theorem ofInt_zetaNat (k : Nat) : ofInt (zetaNat k : Int)=zetas k := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [VG.Proof.MlDsa.KeyGen.ofInt_val]
  rw [Int.emod_eq_of_lt (by omega) (by have := zetaNat_lt k; change _<8380417 at this; omega)]
  exact congrArg (fun n : Nat => (n : Int)) (zetaNat_eq k)

theorem schedule_to_field (ops : List Op) (w : IPoly) (hv : ops.all valid=true) :
    toRq ((ops.map Op.toButterfly).foldl (fun p o => lazyBfly p o.index o.length o.root) w)=
      run ops (toRq w) := by
  rw [schedule_field _ _ (by
    intro o ho
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ho
    exact of_decide_eq_true ((List.all_eq_true.mp hv) a ha))]
  rw [List.foldl_map]
  have hf : (fun (p : Poly) (o : Op) => bfly p o.toButterfly.index o.toButterfly.length
      (ofInt o.toButterfly.root)) = (fun p o => o.apply p) := by
    funext p o
    change bfly p o.index o.length (ofInt (zetaNat o.rootIndex : Int)) =
      bfly p o.index o.length (zetas o.rootIndex)
    rw [ofInt_zetaNat]
  exact congrArg (fun f => ops.foldl f (toRq w)) hf

/-- Integer lazy butterfly traversal has exactly the standard field result. -/
theorem traversal_field (w : IPoly) :
    toRq (((outerSchedule++innerSchedule).map Op.toButterfly).foldl
      (fun p o => lazyBfly p o.index o.length o.root) w)=ntt (toRq w) := by
  rw [schedule_to_field _ _ (by simp only [List.all_append,outer_valid,inner_valid,Bool.and_self]),
    run_append,traversal_ntt]

end VG.Proof.MlDsa.AArch64.Optimized.Traversal

end
