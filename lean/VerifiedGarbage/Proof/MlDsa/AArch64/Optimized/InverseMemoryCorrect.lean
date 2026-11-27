module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCore
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalBank
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalSlice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseArithmetic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStage
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Arithmetic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly

/-! ### `MlDsa.AArch64.Optimized.InverseBankFieldStage`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseTraversalCorrect`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseTraversalChecked`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

theorem local_checked :
    Schedule.check key mask ((List.range 8).map localSlice) = some standardLocal := by
  decide +kernel

theorem strided_checked :
    Schedule.check key mask ((List.range 8).map stridedSlice) = some standardStrided := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

end

end


/-! ## From `InverseTraversalSpec.lean` -/

@[expose] public section

section

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

end

/-! ## From `InverseTraversalCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem local_run (w : Poly) : run localSchedule w=run standardLocal w :=
  (Schedule.check_run (fun _ _ h => mask_comm h) local_checked w).symm

theorem strided_run (w : Poly) : run stridedSchedule w=run standardStrided w :=
  (Schedule.check_run (fun _ _ h => mask_comm h) strided_checked w).symm

/-- Independent local five-layer blocks followed by strided three-layer slices
are Algorithm 42, before its final coefficient scaling. -/
theorem traversal_nttInv (w : Poly) :
    (run stridedSchedule (run localSchedule w)).map (· * 8347681)=nttInv w := by
  rw [local_run,strided_run,← run_append,standard_inverse]

/-- The selected inverse uses R/256 instead of 1/256, compensating a preceding
Montgomery point product. This changes only the internal representation. -/
theorem traversal_montgomery (w : Poly) :
    (run stridedSchedule (run localSchedule w)).map (· * 16382)=montgomeryNttInv w := by
  rw [montgomeryNttInv,← traversal_nttInv]
  rw [Vector.map_map]
  have h : (8347681 : Zq)*montgomeryR=16382 := by decide +kernel
  simp only [Function.comp_def,Fin.mul_assoc,h]

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

end

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseTraversalField`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith


namespace InverseTraversal

theorem ofInt_negZetaNat (k : Nat) : ofInt (negZetaNat k : Int) = -zetas k := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [VG.Proof.MlDsa.KeyGen.ofInt_val]
  rw [Int.emod_eq_of_lt (by omega_using []) (by have := negZetaNat_lt k; change _<8380417 at this; omega_using [this])]
  exact congrArg (fun n : Nat => (n : Int)) (negZetaNat_eq k)

end InverseTraversal

end VG.Proof.MlDsa.AArch64.Optimized

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseBankFieldGroups`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def innerLoc (u i e : Nat) : Nat := 32*u+4*i+e

def innerRegBlock (w : Poly) (base gap u : Nat) (z : Zq) (t : Nat) : Poly :=
  (List.range t).foldl (fun w j => blockN bflyInv w (4*gap) z (innerLoc u (base+j) 0) 4) w

/-- A register group's first t butterflies update exactly its selected register
pairs, independently in each of the four lanes. -/
theorem innerRegBlock_get (w : Poly) {base gap u t : Nat} (hgap : 0<gap)
    (hb : base+2*gap≤8) (hu : u<8) (ht : t≤gap) (z : Zq)
    {i e : Nat} (hi : i<8) (he : e<4) :
    (innerRegBlock w base gap u z t)[innerLoc u i e]! =
      if base≤i ∧ i<base+t then w[innerLoc u i e]! + w[innerLoc u (i+gap) e]!
      else if base+gap≤i ∧ i<base+gap+t then z*(w[innerLoc u (i-gap) e]! - w[innerLoc u i e]!)
      else w[innerLoc u i e]! := by
  induction t generalizing i with
  | zero =>
    simp only [innerRegBlock,List.range_zero,List.foldl_nil,Nat.add_zero]
    rw [ite_eq_right (by omega_using []),ite_eq_right (by omega_using [])]
  | succ t ih =>
    rw [innerRegBlock,foldl_range_succ]
    change (blockN bflyInv (innerRegBlock w base gap u z t) (4*gap) z (innerLoc u (base+t) 0) 4)[innerLoc u i e]! = _
    rw [blockN_bflyInv_get' _ (by omega_using [hgap]) (by omega_using [hgap]) (by unfold innerLoc n; omega_using [hb, hu, ht]) (by unfold innerLoc n; omega_using [hu, he, hi])]
    by_cases ha : i=base+t
    · subst i
      rw [ite_eq_left (by unfold innerLoc; omega_using [he]),
        show innerLoc u (base+t) e+4*gap=innerLoc u (base+t+gap) e by unfold innerLoc; omega_using [],
        ih (by omega_using [ht]) hi, ih (by omega_using [ht]) (by omega_using [hb, ht])]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · by_cases hd : i=base+t+gap
      · subst i
        rw [ite_eq_right (by unfold innerLoc; omega_using [hgap]),ite_eq_left (by unfold innerLoc; omega_using [he]),
          show innerLoc u (base+t+gap) e-4*gap=innerLoc u (base+t) e by unfold innerLoc; omega_using [],
          ih (by omega_using [ht]) hi,ih (by omega_using [ht]) (by omega_using [hb, ht])]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
        rw [Nat.add_sub_cancel]
      · rw [ite_eq_right (by unfold innerLoc; omega_using [he, ha]),ite_eq_right (by unfold innerLoc; omega_using [he, hd]),ih (by omega_using [ht]) hi]
        have h1 : (base≤i ∧ i<base+t) ↔ (base≤i ∧ i<base+(t+1)) := by omega_using [ha]
        have h2 : (base+gap≤i ∧ i<base+gap+t) ↔ (base+gap≤i ∧ i<base+gap+(t+1)) := by omega_using [hd]
        simp only [h1,h2]

def innerRegGroupSchedule (u base gap rootIndex : Nat) : List Op :=
  (List.range gap).flatMap fun j => (List.range 4).map fun e =>
    ⟨innerLoc u (base+j) e,4*gap,rootIndex⟩

theorem run_innerRegGroup (w : Poly) (u base gap rootIndex : Nat) :
    run (innerRegGroupSchedule u base gap rootIndex) w=
      innerRegBlock w base gap u (-zetas rootIndex) gap := by
  unfold run innerRegGroupSchedule innerRegBlock
  rw [List.foldl_flatMap]
  apply congrArg (fun f => (List.range gap).foldl f w)
  funext p j
  rw [List.foldl_map]
  unfold blockN
  rw [List.range'_eq_map_range,List.foldl_map]
  apply congrArg (fun f => (List.range 4).foldl f p)
  funext p e
  change bflyInv p (innerLoc u (base+j) e) (4*gap) (-zetas rootIndex)=
    bflyInv p (innerLoc u (base+j) 0+e) (4*gap) (-zetas rootIndex)
  rw [innerLoc,innerLoc,Nat.add_zero]

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def stageDepth (i k : Nat) : Nat :=
  if i<4 then if k<2*i then 1 else 0
  else if i<6 then if k<4*(i-4) then 2 else 1
  else if i=6 then 2 else 3

def StageBound (v : Vector (BitVec 128) 8) (i : Nat) (b : Int) : Prop :=
  ∀ k : Fin 8, ∀ e<4,
    -(2^(stageDepth i k.val)*b)≤(vword v[k.val] e).toInt ∧
      (vword v[k.val] e).toInt≤2^(stageDepth i k.val)*b

theorem stage_depth_geometry (i : Fin 7) (k : Fin 8) :
    if leftSide i.val k.val ∨ rightSide i.val k.val then
      stageDepth i.val (leftSource i.val k).val=stageDepth i.val (rightSource i.val k).val ∧
      stageDepth (i.val+1) k.val=stageDepth i.val (leftSource i.val k).val+1 ∧
      stageDepth i.val (leftSource i.val k).val<3
    else stageDepth (i.val+1) k.val=stageDepth i.val k.val := by
  exact (show ∀ i : Fin 7, ∀ k : Fin 8,
    if leftSide i.val k.val ∨ rightSide i.val k.val then
      stageDepth i.val (leftSource i.val k).val=stageDepth i.val (rightSource i.val k).val ∧
      stageDepth (i.val+1) k.val=stageDepth i.val (leftSource i.val k).val+1 ∧
      stageDepth i.val (leftSource i.val k).val<3
    else stageDepth (i.val+1) k.val=stageDepth i.val k.val by decide +kernel) i k

theorem stageValues_word (i : Nat) (v : Vector (BitVec 128) 8) (z : Nat → Int)
    (k : Fin 8) {e : Nat} (he : e<4) :
    vword (stageValues i v z)[k.val] e=
      let a := vword v[(leftSource i k).val] e
      let b := vword v[(rightSource i k).val] e
      if leftSide i k.val then a+b
      else if rightSide i k.val then fastMulWord (a-b) (z e)
      else vword v[k.val] e := by
  simp only [stageValues,Vector.getElem_ofFn]
  split
  · exact vword_map2 _ _ _ he
  · split
    · rw [fastVector_word _ _ he,vword_map2 _ _ _ he]
    · rfl

theorem stage_bound_safe {b : Int} (hb : 8380417≤b) (hs : 8*b<2147483648)
    {d : Nat} (hd : d<3) : 8380417≤2^d*b ∧ 2*(2^d*b)<2147483648 := by
  have hh : d=0 ∨ d=1 ∨ d=2 := by omega_using [hd]
  rcases hh with rfl | rfl | rfl <;> simp only [Int.reducePow] <;> omega_using [hb, hs]

theorem stageValues_bound (i : Fin 7) (v : Vector (BitVec 128) 8) (z : Nat → Int)
    {b : Int} (hb : 8380417≤b) (hs : 8*b<2147483648) (hv : StageBound v i.val b) :
    StageBound (stageValues i.val v z) (i.val+1) b := by
  intro k e he
  rw [stageValues_word _ _ _ _ he]
  have hg := stage_depth_geometry i k
  by_cases ha : leftSide i.val k.val ∨ rightSide i.val k.val
  · rw [ite_eq_left ha] at hg
    have hl := hv (leftSource i.val k) e he
    have hr := hv (rightSource i.val k) e he
    rw [← hg.1] at hr
    have hsafe := stage_bound_safe hb hs hg.2.2
    have hw := pair_word (vword v[(leftSource i.val k).val] e)
      (vword v[(rightSource i.val k).val] e) (z e) hsafe.1 hsafe.2 hl hr
    have hp := pair_bounds (z := z e) hsafe.1 hsafe.2 hl hr
    have heq : 2^(stageDepth (i.val+1) k.val)*b=2*(2^(stageDepth i.val (leftSource i.val k).val)*b) := by
      rw [hg.2.1,Int.pow_succ,Int.mul_comm _ 2,Int.mul_assoc]
    rw [heq]
    by_cases hleft : leftSide i.val k.val
    · rw [ite_eq_left hleft,hw.1]
      simpa only [Int.neg_mul] using hp.1
    · rw [ite_eq_right hleft,ite_eq_left (ha.resolve_left hleft),hw.2]
      simpa only [Int.neg_mul] using hp.2
  · rw [ite_eq_right ha] at hg
    rw [ite_eq_right (fun h => ha (Or.inl h)),ite_eq_right (fun h => ha (Or.inr h)),hg]
    exact hv k e he

theorem source_geometry (i : Fin 7) (k : Fin 8) :
    if leftSide i.val k.val then
      (leftSource i.val k).val=k.val ∧ (rightSource i.val k).val=k.val+steps[i.val]!.1
    else if rightSide i.val k.val then
      (leftSource i.val k).val=k.val-steps[i.val]!.1 ∧ (rightSource i.val k).val=k.val
    else True := by
  exact (show ∀ i : Fin 7, ∀ k : Fin 8,
    if leftSide i.val k.val then
      (leftSource i.val k).val=k.val ∧ (rightSource i.val k).val=k.val+steps[i.val]!.1
    else if rightSide i.val k.val then
      (leftSource i.val k).val=k.val-steps[i.val]!.1 ∧ (rightSource i.val k).val=k.val
    else True by decide +kernel) i k

theorem step_bounds (i : Fin 7) :
    0<steps[i.val]!.1 ∧ 2*steps[i.val]!.1*steps[i.val]!.2+2*steps[i.val]!.1≤8 := by
  exact (show ∀ i : Fin 7,
    0<steps[i.val]!.1 ∧ 2*steps[i.val]!.1*steps[i.val]!.2+2*steps[i.val]!.1≤8 by decide +kernel) i

def stageOps (u root i : Nat) : List InverseTraversal.Op :=
  InverseTraversal.innerRegGroupSchedule u (2*steps[i]!.1*steps[i]!.2) steps[i]!.1 root

theorem stageValues_field (i : Fin 7) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (root : Nat) {b : Int}
    (hb : 8380417≤b) (hs : 8*b<2147483648) (hv : StageBound v i.val b)
    (hf : InnerBankField u v w) :
    InnerBankField u (stageValues i.val v (fun _ => (negZetaNat root : Int)))
      (InverseTraversal.run (stageOps u root i.val) w) := by
  intro k e he
  rw [stageValues_word _ _ _ _ he]
  change ofInt (_ : BitVec 32).toInt =
    (InverseTraversal.run (stageOps u root i.val) w)[InverseTraversal.innerLoc u k.val e]!
  rw [stageOps,InverseTraversal.run_innerRegGroup,
    InverseTraversal.innerRegBlock_get _ (step_bounds i).1 (step_bounds i).2 hu (Nat.le_refl _) _ k.isLt he]
  rw [show 2*steps[i.val]!.1*steps[i.val]!.2+steps[i.val]!.1+steps[i.val]!.1=
      2*steps[i.val]!.1*steps[i.val]!.2+2*steps[i.val]!.1 by omega_using []]
  change ofInt (_ : BitVec 32).toInt =
    if leftSide i.val k.val then
      w[InverseTraversal.innerLoc u k.val e]! + w[InverseTraversal.innerLoc u (k.val+steps[i.val]!.1) e]!
    else if rightSide i.val k.val then -zetas root *
      (w[InverseTraversal.innerLoc u (k.val-steps[i.val]!.1) e]! - w[InverseTraversal.innerLoc u k.val e]!)
    else w[InverseTraversal.innerLoc u k.val e]!
  have hg := stage_depth_geometry i k
  have hsrc := source_geometry i k
  by_cases ha : leftSide i.val k.val ∨ rightSide i.val k.val
  · rw [ite_eq_left ha] at hg
    have hl := hv (leftSource i.val k) e he
    have hr := hv (rightSource i.val k) e he
    rw [← hg.1] at hr
    have hsafe := stage_bound_safe hb hs hg.2.2
    have hw := pair_word (vword v[(leftSource i.val k).val] e)
      (vword v[(rightSource i.val k).val] e) (negZetaNat root : Int) hsafe.1 hsafe.2 hl hr
    have hleft := hf (leftSource i.val k) e he
    have hright := hf (rightSource i.val k) e he
    by_cases hL : leftSide i.val k.val
    · rw [ite_eq_left hL] at hsrc
      rw [ite_eq_left hL,hw.1]
      simp only [pair]
      rw [ofInt_add,hleft,hright,ite_eq_left hL]
      simp only [Traversal.innerLoc,InverseTraversal.innerLoc,hsrc.1,hsrc.2]
    · have hR := ha.resolve_left hL
      rw [ite_eq_right hL,ite_eq_left hR] at hsrc
      rw [ite_eq_right hL,ite_eq_left hR,hw.2]
      simp only [pair]
      rw [fastMul_field,ofInt_sub,InverseTraversal.ofInt_negZetaNat,hleft,hright,
        ite_eq_right hL,ite_eq_left hR,Fin.mul_comm]
      simp only [Traversal.innerLoc,InverseTraversal.innerLoc,hsrc.1,hsrc.2]
  · rw [ite_eq_right (fun h => ha (Or.inl h)),ite_eq_right (fun h => ha (Or.inr h))]
    rw [ite_eq_right (fun h => ha (Or.inl h)),ite_eq_right (fun h => ha (Or.inr h))]
    exact hf k e he

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseFinalBankFieldStage`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseFinalBankFieldGroups`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def stridedLoc (u i e : Nat) : Nat := 32*i+4*u+e

def stridedRegBlock (w : Poly) (base gap u : Nat) (z : Zq) (t : Nat) : Poly :=
  (List.range t).foldl (fun w j => blockN bflyInv w (32*gap) z (stridedLoc u (base+j) 0) 4) w

/-- A register group's first t butterflies update exactly its selected register
pairs, independently in each of the four lanes. -/
theorem stridedRegBlock_get (w : Poly) {base gap u t : Nat} (hgap : 0<gap)
    (hb : base+2*gap≤8) (hu : u<8) (ht : t≤gap) (z : Zq)
    {i e : Nat} (hi : i<8) (he : e<4) :
    (stridedRegBlock w base gap u z t)[stridedLoc u i e]! =
      if base≤i ∧ i<base+t then w[stridedLoc u i e]! + w[stridedLoc u (i+gap) e]!
      else if base+gap≤i ∧ i<base+gap+t then z*(w[stridedLoc u (i-gap) e]! - w[stridedLoc u i e]!)
      else w[stridedLoc u i e]! := by
  induction t generalizing i with
  | zero =>
    simp only [stridedRegBlock,List.range_zero,List.foldl_nil,Nat.add_zero]
    rw [ite_eq_right (by omega_using []),ite_eq_right (by omega_using [])]
  | succ t ih =>
    rw [stridedRegBlock,foldl_range_succ]
    change (blockN bflyInv (stridedRegBlock w base gap u z t) (32*gap) z (stridedLoc u (base+t) 0) 4)[stridedLoc u i e]! = _
    rw [blockN_bflyInv_get' _ (by omega_using [hgap]) (by omega_using [hgap]) (by unfold stridedLoc n; omega_using [hb, hu, ht]) (by unfold stridedLoc n; omega_using [hu, he, hi])]
    by_cases ha : i=base+t
    · subst i
      rw [ite_eq_left (by unfold stridedLoc; omega_using [he]),
        show stridedLoc u (base+t) e+32*gap=stridedLoc u (base+t+gap) e by unfold stridedLoc; omega_using [],
        ih (by omega_using [ht]) hi, ih (by omega_using [ht]) (by omega_using [hb, ht])]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · by_cases hd : i=base+t+gap
      · subst i
        rw [ite_eq_right (by unfold stridedLoc; omega_using [hgap]),ite_eq_left (by unfold stridedLoc; omega_using [he]),
          show stridedLoc u (base+t+gap) e-32*gap=stridedLoc u (base+t) e by unfold stridedLoc; omega_using [],
          ih (by omega_using [ht]) hi,ih (by omega_using [ht]) (by omega_using [hb, ht])]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
        rw [Nat.add_sub_cancel]
      · rw [ite_eq_right (by unfold stridedLoc; omega_using [he, ha]),ite_eq_right (by unfold stridedLoc; omega_using [he, hd]),ih (by omega_using [ht]) hi]
        have h1 : (base≤i ∧ i<base+t) ↔ (base≤i ∧ i<base+(t+1)) := by omega_using [ha]
        have h2 : (base+gap≤i ∧ i<base+gap+t) ↔ (base+gap≤i ∧ i<base+gap+(t+1)) := by omega_using [hd]
        simp only [h1,h2]

def stridedRegGroupSchedule (u base gap rootIndex : Nat) : List Op :=
  (List.range gap).flatMap fun j => (List.range 4).map fun e =>
    ⟨stridedLoc u (base+j) e,32*gap,rootIndex⟩

theorem run_stridedRegGroup (w : Poly) (u base gap rootIndex : Nat) :
    run (stridedRegGroupSchedule u base gap rootIndex) w=
      stridedRegBlock w base gap u (-zetas rootIndex) gap := by
  unfold run stridedRegGroupSchedule stridedRegBlock
  rw [List.foldl_flatMap]
  apply congrArg (fun f => (List.range gap).foldl f w)
  funext p j
  rw [List.foldl_map]
  unfold blockN
  rw [List.range'_eq_map_range,List.foldl_map]
  apply congrArg (fun f => (List.range 4).foldl f p)
  funext p e
  change bflyInv p (stridedLoc u (base+j) e) (32*gap) (-zetas rootIndex)=
    bflyInv p (stridedLoc u (base+j) 0+e) (32*gap) (-zetas rootIndex)
  rw [stridedLoc,stridedLoc,Nat.add_zero]

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def stridedStageOps (u root i : Nat) : List InverseTraversal.Op :=
  InverseTraversal.stridedRegGroupSchedule u (2*steps[i]!.1*steps[i]!.2) steps[i]!.1 root

theorem stridedStageValues_field (i : Fin 7) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (root : Nat) {b : Int}
    (hb : 8380417≤b) (hs : 8*b<2147483648) (hv : StageBound v i.val b)
    (hf : BankField u v w) :
    BankField u (stageValues i.val v (fun _ => (negZetaNat root : Int)))
      (InverseTraversal.run (stridedStageOps u root i.val) w) := by
  intro k e he
  rw [stageValues_word _ _ _ _ he]
  change ofInt (_ : BitVec 32).toInt =
    (InverseTraversal.run (stridedStageOps u root i.val) w)[InverseTraversal.stridedLoc u k.val e]!
  rw [stridedStageOps,InverseTraversal.run_stridedRegGroup,
    InverseTraversal.stridedRegBlock_get _ (step_bounds i).1 (step_bounds i).2 hu (Nat.le_refl _) _ k.isLt he]
  rw [show 2*steps[i.val]!.1*steps[i.val]!.2+steps[i.val]!.1+steps[i.val]!.1=
      2*steps[i.val]!.1*steps[i.val]!.2+2*steps[i.val]!.1 by omega_using []]
  change ofInt (_ : BitVec 32).toInt =
    if leftSide i.val k.val then
      w[InverseTraversal.stridedLoc u k.val e]! + w[InverseTraversal.stridedLoc u (k.val+steps[i.val]!.1) e]!
    else if rightSide i.val k.val then -zetas root *
      (w[InverseTraversal.stridedLoc u (k.val-steps[i.val]!.1) e]! - w[InverseTraversal.stridedLoc u k.val e]!)
    else w[InverseTraversal.stridedLoc u k.val e]!
  have hg := stage_depth_geometry i k
  have hsrc := source_geometry i k
  by_cases ha : leftSide i.val k.val ∨ rightSide i.val k.val
  · rw [ite_eq_left ha] at hg
    have hl := hv (leftSource i.val k) e he
    have hr := hv (rightSource i.val k) e he
    rw [← hg.1] at hr
    have hsafe := stage_bound_safe hb hs hg.2.2
    have hw := pair_word (vword v[(leftSource i.val k).val] e)
      (vword v[(rightSource i.val k).val] e) (negZetaNat root : Int) hsafe.1 hsafe.2 hl hr
    have hleft := hf (leftSource i.val k) e he
    have hright := hf (rightSource i.val k) e he
    by_cases hL : leftSide i.val k.val
    · rw [ite_eq_left hL] at hsrc
      rw [ite_eq_left hL,hw.1]
      simp only [pair]
      rw [ofInt_add,hleft,hright,ite_eq_left hL]
      simp only [Traversal.loc,InverseTraversal.stridedLoc,hsrc.1,hsrc.2]
    · have hR := ha.resolve_left hL
      rw [ite_eq_right hL,ite_eq_left hR] at hsrc
      rw [ite_eq_right hL,ite_eq_left hR,hw.2]
      simp only [pair]
      rw [fastMul_field,ofInt_sub,InverseTraversal.ofInt_negZetaNat,hleft,hright,
        ite_eq_right hL,ite_eq_left hR,Fin.mul_comm]
      simp only [Traversal.loc,InverseTraversal.stridedLoc,hsrc.1,hsrc.2]
  · rw [ite_eq_right (fun h => ha (Or.inl h)),ite_eq_right (fun h => ha (Or.inr h))]
    rw [ite_eq_right (fun h => ha (Or.inl h)),ite_eq_right (fun h => ha (Or.inr h))]
    exact hf k e he

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseBankField`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseBankFieldSchedule`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedSchedule (start len : Nat) (root : Nat → Nat) : List Op :=
  (List.range (4/len)).flatMap fun g => (List.range len).map fun j =>
    ⟨start+2*len*g+j,len,root (len*g+j)⟩

theorem packedSchedule_get (w : Poly) {start len i : Nat} (hl : len=1 ∨ len=2)
    (hs : start+8≤256) (hi : i<8) (root : Nat → Nat) :
    (run (packedSchedule start len root) w)[start+i]! =
      let x := w[start+packedLow len i]!
      let y := w[start+packedLow len i+len]!
      if i%(2*len)<len then x+y else -zetas (root (packedLane len i))*(x-y) := by
  have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega_using [hi]
  rcases hl with rfl | rfl <;>
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [-getElem!_pos,packedSchedule,run,List.range_succ,Op.apply,packedLow,packedLane,Nat.add_assoc] <;>
    repeat (rw [bflyInv_get _ (by omega_using []) (by unfold n; omega_using [hs]) _ (by unfold n; omega_using [hs])]
            simp (disch := omega) [-getElem!_pos,Nat.add_assoc])

theorem packedSchedule_outside (w : Poly) {start len i : Nat} (hl : len=1 ∨ len=2)
    (hs : start+8≤256) (hi : i<256) (hout : i<start ∨ start+8≤i) (root : Nat → Nat) :
    (run (packedSchedule start len root) w)[i]! = w[i]! := by
  have h0 : i≠start := by omega_using [hout]
  have hn : ∀ j<8,i≠start+j := by intro j hj; omega_using [hout, hj]
  rcases hl with rfl | rfl <;>
    simp [-getElem!_pos,packedSchedule,run,List.range_succ,Op.apply] <;>
    repeat (rw [bflyInv_get _ (by omega_using []) (by unfold n; omega_using [hs]) _ (by unfold n; omega_using [hi])]
            simp (disch := omega) [-getElem!_pos,Nat.add_assoc,h0,hn 1 (by decide),
              hn 2 (by decide),hn 3 (by decide),hn 4 (by decide),hn 5 (by decide),
              hn 6 (by decide),hn 7 (by decide)])

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseBankFieldRun`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def runOps (u : Nat) (root : Nat → Nat) (i : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => stageOps u (root i) i ++ runOps u root (i+1) n

theorem runValues_field (i n : Nat) (hin : i+n≤7) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (root : Nat → Nat) {b : Int}
    (hb : 8380417≤b) (hs : 8*b<2147483648) (hv : StageBound v i b)
    (hf : InnerBankField u v w) :
    StageBound (runValues (fun i _ => (negZetaNat (root i) : Int)) i n v) (i+n) b ∧
      InnerBankField u (runValues (fun i _ => (negZetaNat (root i) : Int)) i n v)
        (InverseTraversal.run (runOps u root i n) w) := by
  induction n generalizing i v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hi : i<7 := by omega_using [hin]
    have hp := stageValues_bound ⟨i,hi⟩ v (fun _ => (negZetaNat (root i) : Int)) hb hs hv
    have hfield := stageValues_field ⟨i,hi⟩ v w hu (root i) hb hs hv hf
    have h := ih (i := i+1) (by omega_using [hin]) _ _ hp hfield
    simpa only [runValues,runOps,InverseTraversal.run_append,Nat.add_assoc,Nat.add_comm 1 n] using h

theorem stageBound_zero (v : Vector (BitVec 128) 8) (b : Int) :
    StageBound v 0 b ↔ BankBound v b := by
  simp only [StageBound,BankBound,stageDepth,Nat.reduceLT,ite_true,Nat.mul_zero,
    Nat.not_lt_zero,ite_false,Int.pow_zero,Int.one_mul]

theorem stageBound_seven (v : Vector (BitVec 128) 8) (b : Int) :
    StageBound v 7 b ↔ BankBound v (8*b) := by
  simp only [StageBound,BankBound,stageDepth,Nat.reduceLT,ite_false,Nat.reduceEqDiff,Int.reducePow]

theorem localRoot_index (u : Nat) :
    localRoot u=(fun i _ => (negZetaNat (localIndex u i) : Int)) := rfl

theorem runValues_local (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 33521668) (hf : InnerBankField u v w) :
    BankBound (runValues (localRoot u) 0 7 v) 268173344 ∧
      InnerBankField u (runValues (localRoot u) 0 7 v)
        (InverseTraversal.run (runOps u (localIndex u) 0 7) w) := by
  rw [localRoot_index]
  have h := runValues_field 0 7 (by decide) v w hu (localIndex u) (by decide) (by decide)
    ((stageBound_zero v 33521668).mpr hv) hf
  exact ⟨(stageBound_seven _ _).mp h.1,h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseBankFieldPackedBank`, which only this module used -/

section

/-! ## From `InverseBankFieldPacked.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

/-- The packed inverse gather/scatter computes four ordered scalar butterflies. -/
theorem packedResult_word (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) :
    vword (packedResult len second a b z) e =
      let i := (if second then 4 else 0)+e
      let x := pairWord a b (packedLow len i)
      let y := pairWord a b (packedLow len i+len)
      if i%(2*len)<len then x+y else fastMulWord (x-y) (z (packedLane len i)) := by
  have he' : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
  rcases hl with rfl | rfl <;> cases second <;>
    rcases he' with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) [packedResult,gather,scatter,
      vword_trn1_d2,vword_trn2_d2,vword_zip1_s4',vword_zip2_s4,
      VG.AArch64.vword_map2,fastVector_word,vword_uzp1_s4,vword_uzp2_s4,
      pairWord,packedLow,packedLane]

/-- Bounds are needed only for the two selected registers, not the other six
registers whose current layer may already have completed. -/
theorem packedResult_int (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hq : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    (vword (packedResult len second a b z) e).toInt =
      let i := (if second then 4 else 0)+e
      let x := (pairWord a b (packedLow len i)).toInt
      let y := (pairWord a b (packedLow len i+len)).toInt
      if i%(2*len)<len then x+y else fastMul (x-y) (z (packedLane len i)) := by
  rw [packedResult_word a b hl second z he]
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega_using [he]
  have hd := packed_indices hl hi
  have hp := pair_word (z := z (packedLane len ((if second then 4 else 0)+e)))
    _ _ hq hs (hv _ hd.1) (hv _ hd.2.1)
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc]
    exact hp.1
  · rw [ite_eq_right hc,ite_eq_right hc]
    exact hp.2

theorem packedResult_bound (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hq : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    -(2*bound)≤(vword (packedResult len second a b z) e).toInt ∧
      (vword (packedResult len second a b z) e).toInt≤2*bound := by
  rw [packedResult_int a b hl second z he hq hs hv]
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega_using [he]
  have hd := packed_indices hl hi
  have hp := pair_bounds (z := z (packedLane len ((if second then 4 else 0)+e)))
    hq hs (hv _ hd.1) (hv _ hd.2.1)
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc]
    simpa only [pair,Int.neg_mul] using hp.1
  · rw [ite_eq_right hc]
    simpa only [pair,Int.neg_mul] using hp.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankFieldPackedField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedResult_field (a b : BitVec 128) (w : Poly) {len start : Nat}
    (hl : len=1 ∨ len=2) (hstart : start+8≤256) (second : Bool) (root : Nat → Nat)
    {e : Nat} (he : e<4) {bound : Int} (hb : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound)
    (hf : ∀ i<8,ofInt (pairWord a b i).toInt=w[start+i]!) :
    ofInt (vword (packedResult len second a b (fun e => (negZetaNat (root e) : Int))) e).toInt=
      (InverseTraversal.run (InverseTraversal.packedSchedule start len root) w)[start+(if second then 4 else 0)+e]! := by
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega_using [he]
  have hd := packed_indices hl hi
  rw [packedResult_int a b hl second _ he hb hs hv,Nat.add_assoc,
    InverseTraversal.packedSchedule_get w hl hstart hi]
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc,ofInt_add,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc]
  · rw [ite_eq_right hc,ite_eq_right hc,fastMul_field,ofInt_sub,
      InverseTraversal.ofInt_negZetaNat,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc,Fin.mul_comm]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankFieldPackedBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedValues_field (v : Vector (BitVec 128) 8) (w : Poly) {g len u : Nat}
    (hg : g<4) (hl : len=1 ∨ len=2) (hu : u<8) (root : Nat → Nat) {bound : Int}
    (hb : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ j<8, -bound≤(pairWord v[2*g] v[2*g+1] j).toInt ∧
      (pairWord v[2*g] v[2*g+1] j).toInt≤bound)
    (hf : InnerBankField u v w) :
    InnerBankField u (packedValues v ⟨2*g,by omega_using [hg]⟩ ⟨2*g+1,by omega_using [hg]⟩ len
      (fun e => (negZetaNat (root e) : Int)))
      (InverseTraversal.run (InverseTraversal.packedSchedule (32*u+8*g) len root) w) := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj]
    have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega_using [hg, hu])
      true root he hb hs hv
      (fun i hi => pairWord_field v w hg hf hi)
    simpa only [ite_true,Traversal.innerLoc,← hj,show 32*u+4*(2*g+1)+e=32*u+8*g+4+e by omega_using []] using h
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi]
      have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega_using [hg, hu])
        false root he hb hs hv
        (fun i hi => pairWord_field v w hg hf hi)
      simpa only [Bool.false_eq_true,ite_false,Nat.add_zero,Traversal.innerLoc,← hi,
        show 4*(2*g)=8*g by omega_using []] using h
    · rw [ite_eq_right hi,InverseTraversal.packedSchedule_outside w hl (by omega_using [hg, hu])
        (by unfold Traversal.innerLoc; omega_using [hu, he]) (by unfold Traversal.innerLoc; omega_using [he, hj, hi]),hf i e he]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end

/-! ## From `InverseBankFieldPackedLayer.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/InverseBankFieldPackedBounds.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64

/-- A packed layer doubles the bound only for the register pairs it has
already processed; the following pair still has the old bound. -/
def PackedProgress (v : Vector (BitVec 128) 8) (g : Nat) (b : Int) : Prop :=
  ∀ i : Fin 8, ∀ e<4,
    -(if i.val<2*g then 2*b else b)≤(vword v[i.val] e).toInt ∧
      (vword v[i.val] e).toInt≤(if i.val<2*g then 2*b else b)

theorem PackedProgress.pair {v : Vector (BitVec 128) 8} {g : Nat} {b : Int}
    (h : PackedProgress v g b) (hg : g<4) {i : Nat} (hi : i<8) :
    -b≤(pairWord v[2*g] v[2*g+1] i).toInt ∧ (pairWord v[2*g] v[2*g+1] i).toInt≤b := by
  unfold pairWord
  split
  · have hv := h ⟨2*g,by omega_using [hg]⟩ i ‹_›
    simpa only [show ¬2*g<2*g by omega_using [],ite_false] using hv
  · have hv := h ⟨2*g+1,by omega_using [hg]⟩ (i-4) (by omega_using [hi])
    simpa only [show ¬2*g+1<2*g by omega_using [],ite_false] using hv

theorem packedValues_progress (v : Vector (BitVec 128) 8) {g len : Nat} (hg : g<4)
    (hl : len=1 ∨ len=2) (z : Nat → Int) {b : Int} (hb : 8380417≤b)
    (hs : 2*b<2147483648) (hv : PackedProgress v g b) :
    PackedProgress (packedValues v ⟨2*g,by omega_using [hg]⟩ ⟨2*g+1,by omega_using [hg]⟩ len z) (g+1) b := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj,ite_eq_left (by omega_using [hj] : i.val<2*(g+1))]
    exact packedResult_bound _ _ hl true z he hb hs (fun j hj => hv.pair hg hj)
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi,ite_eq_left (by omega_using [hi] : i.val<2*(g+1))]
      exact packedResult_bound _ _ hl false z he hb hs (fun j hj => hv.pair hg hj)
    · rw [ite_eq_right hi]
      have heq : (i.val<2*(g+1)) ↔ (i.val<2*g) := by omega_using [hj, hi]
      simpa only [heq] using hv i e he

theorem packedProgress_zero (v : Vector (BitVec 128) 8) (b : Int) :
    PackedProgress v 0 b ↔ BankBound v b := by
  simp only [PackedProgress,BankBound,Nat.mul_zero,Nat.not_lt_zero,ite_false]

theorem packedProgress_four (v : Vector (BitVec 128) 8) (b : Int) :
    PackedProgress v 4 b ↔ BankBound v (2*b) := by
  constructor <;> intro h i e he
  all_goals have hi : i.val<2*4 := i.isLt
  · simpa only [hi,ite_true] using h i e he
  · simpa only [hi,ite_true] using h i e he

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedLayerValues (len : Nat) (root : Nat → Nat → Nat) (g : Nat) :
    Nat → Vector (BitVec 128) 8 → Vector (BitVec 128) 8
  | 0,v => v
  | n+1,v => packedLayerValues len root (g+1) n
      (packedValues v ⟨(2*g)%8,Nat.mod_lt _ (by decide)⟩
        ⟨(2*g+1)%8,Nat.mod_lt _ (by decide)⟩ len (fun e => (negZetaNat (root g e) : Int)))

def packedLayerOps (u len : Nat) (root : Nat → Nat → Nat) (g : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => InverseTraversal.packedSchedule (32*u+8*g) len (root g) ++ packedLayerOps u len root (g+1) n

theorem packedLayer_values (v : Vector (BitVec 128) 8) (w : Poly) {u len g n : Nat}
    (hu : u<8) (hl : len=1 ∨ len=2) (hgn : g+n≤4) (root : Nat → Nat → Nat)
    {b : Int} (hb : 8380417≤b) (hs : 2*b<2147483648)
    (hv : PackedProgress v g b) (hf : InnerBankField u v w) :
    PackedProgress (packedLayerValues len root g n v) (g+n) b ∧
      InnerBankField u (packedLayerValues len root g n v)
        (InverseTraversal.run (packedLayerOps u len root g n) w) := by
  induction n generalizing g v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hg : g<4 := by omega_using [hgn]
    have hm0 : 2*g%8=2*g := Nat.mod_eq_of_lt (by omega_using [hgn])
    have hm1 : (2*g+1)%8=2*g+1 := Nat.mod_eq_of_lt (by omega_using [hgn])
    have hp := packedValues_progress v hg hl (fun e => (negZetaNat (root g e) : Int)) hb hs hv
    have hfield := packedValues_field v w hg hl hu (root g) hb hs
      (fun j hj => hv.pair hg hj) hf
    have hi := ih _ _ (g := g+1) (by omega_using [hgn]) hp hfield
    simpa only [packedLayerValues,packedLayerOps,hm0,hm1,InverseTraversal.run_append,
      Nat.add_assoc,Nat.add_comm 1 n] using hi

theorem packedLayer_full (v : Vector (BitVec 128) 8) (w : Poly) {u len : Nat}
    (hu : u<8) (hl : len=1 ∨ len=2) (root : Nat → Nat → Nat)
    {b : Int} (hb : 8380417≤b) (hs : 2*b<2147483648)
    (hv : BankBound v b) (hf : InnerBankField u v w) :
    BankBound (packedLayerValues len root 0 4 v) (2*b) ∧
      InnerBankField u (packedLayerValues len root 0 4 v)
        (InverseTraversal.run (packedLayerOps u len root 0 4) w) := by
  have h := packedLayer_values v w hu hl (g := 0) (n := 4) (by decide) root hb hs
    ((packedProgress_zero v b).mpr hv) hf
  exact ⟨(packedProgress_four _ b).mp h.1,h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankFieldPackedPass.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedIndex (u len g e : Nat) : Nat :=
  256/len-1-(16*u/len+4*g/len+e/len)

def packedPassValues (u : Nat) (v : Vector (BitVec 128) 8) : Vector (BitVec 128) 8 :=
  packedLayerValues 2 (packedIndex u 2) 0 4 (packedLayerValues 1 (packedIndex u 1) 0 4 v)

def packedPassOps (u : Nat) : List InverseTraversal.Op :=
  packedLayerOps u 1 (packedIndex u 1) 0 4 ++ packedLayerOps u 2 (packedIndex u 2) 0 4

theorem packedPass_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 8380417) (hf : InnerBankField u v w) :
    BankBound (packedPassValues u v) 33521668 ∧
      InnerBankField u (packedPassValues u v) (InverseTraversal.run (packedPassOps u) w) := by
  have h1 := packedLayer_full v w hu (Or.inl rfl) (packedIndex u 1) (by decide) (by decide) hv hf
  have h2 := packedLayer_full _ _ hu (Or.inr rfl) (packedIndex u 2) (by decide) (by decide) h1.1 h1.2
  simpa only [packedPassValues,packedPassOps,InverseTraversal.run_append,Int.reduceMul] using h2

theorem packedRoot_index (u g len : Nat) (hl : len=1 ∨ len=2) :
    packedRoot u g len=(fun e => (negZetaNat (packedIndex u len g e) : Int)) := by
  funext e
  have hi : (if len=1 then 255-16*u-4*g-e else 127-8*u-2*g-e/2)=packedIndex u len g e := by
    rcases hl with rfl | rfl <;> simp [packedIndex] <;> omega_using []
  unfold packedRoot
  rw [hi]
  rfl

theorem packedPassValues_eq (u : Nat) (v : Vector (BitVec 128) 8) :
    packedRunValues v (packedRoot u) packedSteps=packedPassValues u v := by
  have h1 := fun g => packedRoot_index u g 1 (Or.inl rfl)
  have h2 := fun g => packedRoot_index u g 2 (Or.inr rfl)
  simp only [packedRunValues,packedSteps,h1,h2,packedPassValues,packedLayerValues]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The physical packed groups and renamed groups visit exactly the logical
local slice, retaining each root index symbolically. -/
theorem fiveOps_eq {u : Nat} (hu : u<8) :
    packedPassOps u ++ runOps u (localIndex u) 0 7=InverseTraversal.localSlice u := by
  exact (show ∀ u : Fin 8,
    packedPassOps u.val ++ runOps u.val (localIndex u.val) 0 7=InverseTraversal.localSlice u.val
    by decide +kernel) ⟨u,hu⟩

/-- The selected five-layer machine bank has the exact inverse field result,
with every signed representative bounded by 32q. No normalization is added. -/
theorem fiveValues_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 8380417) (hf : InnerBankField u v w) :
    BankBound (fiveValues u v) 268173344 ∧
      InnerBankField u (fiveValues u v) (InverseTraversal.run (InverseTraversal.localSlice u) w) := by
  rw [fiveValues,packedPassValues_eq]
  have hp := packedPass_field v w hu hv hf
  have h := runValues_local _ _ hu hp.1 hp.2
  refine ⟨h.1,?_⟩
  simpa only [← InverseTraversal.run_append,fiveOps_eq hu] using h.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseSliceComposition`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseMemorySchedule`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Every operation stays within its selected slice. -/
def supported (slice : Nat → Nat) (u : Nat) (o : Op) : Bool := decide
  (0<o.length ∧ o.index+o.length<n ∧ slice o.index=u ∧ slice (o.index+o.length)=u)

theorem strided_supported : ∀ u : Fin 8,
    (stridedSlice u.val).all (supported (fun k => k%32/4) u.val)=true := by decide +kernel

theorem local_supported : ∀ u : Fin 8,
    (localSlice u.val).all (supported (fun k => k/32) u.val)=true := by decide +kernel

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
    rw [bflyInv_get w h'.1 h'.2.1 _ hk]
    have h0 : o.index≠k := fun he => ho (he ▸ h'.2.2.1)
    have h1 : o.index+o.length≠k := fun he => ho (he ▸ h'.2.2.2)
    simp only [Ne.symm h0,Ne.symm h1,ite_false]

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

end

end

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

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseMemory`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def firstMemStep (m : Mem) (p : Addr) (u : Nat) : Mem :=
  writeBank (fiveValues u (readBank m (coeffAddr p (32*u)) 16)) (coeffAddr p (32*u)) 16 m

def finalMemStep (m : Mem) (p : Addr) (q : BitVec 128) (u : Nat) : Mem :=
  writeBank (finalValues (readBank m (coeffAddr p (4*u)) 128) q) (coeffAddr p (4*u)) 128 m

theorem firstPassMem_step (m : Mem) (p : Addr) (u : Nat) :
    firstPassMem m p (u+1)=firstMemStep (firstPassMem m p u) p u := by
  simp only [firstPassMem,firstMemStep,coeffAddr,show 4*(32*u)=128*u by omega_using []]

theorem finalPassMem_step (m : Mem) (p : Addr) (q : BitVec 128) (u : Nat) :
    finalPassMem m p q (u+1)=finalMemStep (finalPassMem m p q u) p q u := by
  simp only [finalPassMem,finalMemStep,coeffAddr,show 4*(4*u)=16*u by omega_using []]

theorem firstMemStep_at (m : Mem) (p : Addr) {u : Nat} (hu : u<8) (i : Fin 8)
    {e : Nat} (he : e<4) :
    coeffAt (firstMemStep m p u) p (32*u+4*i.val+e)=
      vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e := by
  exact writeBank_coeff_at _ m p (start := 32*u) (step := 4) (by decide) (by omega_using [hu]) i he

theorem firstMemStep_outside (m : Mem) (p : Addr) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k<32*u ∨ 32*(u+1)≤k) :
    coeffAt (firstMemStep m p u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start := 32*u) (step := 4) _ m p (by omega_using [hu]) hk
  intro i; omega_using [hout]

theorem firstPass_untouched (m : Mem) (p : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : 32*u≤k) :
    coeffAt (firstPassMem m p u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [firstPassMem_step,firstMemStep_outside _ _ (by omega_using [hu]) hk (Or.inr hbefore)]
    exact ih (by omega_using [hu]) (by omega_using [hbefore])

theorem finalMemStep_at (m : Mem) (p : Addr) (q : BitVec 128) {u : Nat}
    (hu : u<8) (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (finalMemStep m p q u) p (4*u+32*i.val+e)=
      vword (finalValues (readBank m (coeffAddr p (4*u)) 128) q)[i.val] e := by
  exact writeBank_coeff_at _ m p (start := 4*u) (step := 32) (by decide) (by omega_using [hu]) i he

theorem finalMemStep_outside (m : Mem) (p : Addr) (q : BitVec 128) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k%32/4≠u) :
    coeffAt (finalMemStep m p q u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start := 4*u) (step := 32) _ m p (by omega_using [hu]) hk
  intro i; omega_using [hu, hout]

theorem finalPass_untouched (m : Mem) (p : Addr) (q : BitVec 128) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : u≤k%32/4) :
    coeffAt (finalPassMem m p q u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [finalPassMem_step,finalMemStep_outside _ _ _ (by omega_using [hu]) hk (by omega_using [hbefore])]
    exact ih (by omega_using [hu]) (by omega_using [hbefore])

/-- A later local block still reads the original, unexpanded input range. -/
theorem firstPass_bank_bound {m : Mem} {p : Addr} {u : Nat} {bound : Int}
    (hu : u<8) (h : ∀ k<n, -bound≤(coeffAt m p k).toInt ∧ (coeffAt m p k).toInt≤bound)
    (i : Fin 8) {e : Nat} (he : e<4) :
    -bound≤(vword (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)[i.val] e).toInt ∧
      (vword (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)[i.val] e).toInt≤bound := by
  rw [readBank_coeff _ p (32*u) 4 i he]
  have hk : 32*u+4*i.val+e<n := by change 32*u+4*i.val+e<256; omega_using [hu, he]
  rw [firstPass_untouched m p (by omega_using [hu]) hk (by omega_using [])]
  exact h _ hk

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseFinalBankFieldFold`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem scaleValues_word (v : Vector (BitVec 128) 8) (k : Fin 8) {e : Nat} (he : e<4) :
    vword (scaleValues v)[k.val] e=
      if k.val<4 then fastMulWord (vword v[k.val] e) 16382 else vword v[k.val] e := by
  simp only [scaleValues,Vector.getElem_ofFn]
  split
  · exact fastVector_word _ _ he
  · rfl

theorem final_sides (k : Fin 8) : (leftSide 6 k.val ↔ k.val<4) ∧ (rightSide 6 k.val ↔ ¬k.val<4) := by
  exact (show ∀ k : Fin 8, (leftSide 6 k.val ↔ k.val<4) ∧ (rightSide 6 k.val ↔ ¬k.val<4) by decide +kernel) k

theorem folded_root_field : ofInt (finalZ 6 0)=ofInt (negZetaNat 1 : Int)*ofInt 16382 := by decide +kernel

theorem folded_lane (v : Vector (BitVec 128) 8) (k : Fin 8) {e : Nat} (he : e<4) :
    let x := vword (scaleValues (stageValues 6 v (finalZ 6)))[k.val] e;
    -8380417<x.toInt ∧ x.toInt<2*8380417 ∧
      ofInt x.toInt=ofInt (vword (stageValues 6 v (fun _ => (negZetaNat 1 : Int)))[k.val] e).toInt*ofInt 16382 := by
  dsimp only
  rw [scaleValues_word _ _ he,stageValues_word _ _ _ _ he]
  simp only [(final_sides k).1,(final_sides k).2]
  by_cases hk : k.val<4
  · rw [ite_eq_left hk,ite_eq_left hk]
    have hb := fastMul_bounds (z := (16382 : Int))
      (BitVec.le_toInt (vword v[(leftSource 6 k).val] e+vword v[(rightSource 6 k).val] e))
      (BitVec.toInt_lt (x := vword v[(leftSource 6 k).val] e+vword v[(rightSource 6 k).val] e))
    rw [fastMulWord_int]
    refine ⟨hb.1,hb.2,?_⟩
    rw [fastMul_field,stageValues_word _ _ _ _ he,ite_eq_left ((final_sides k).1.mpr hk)]
  · rw [ite_eq_right hk,ite_eq_right hk,ite_eq_left hk]
    have hb := fastMul_bounds (z := finalZ 6 e)
      (BitVec.le_toInt (vword v[(leftSource 6 k).val] e-vword v[(rightSource 6 k).val] e))
      (BitVec.toInt_lt (x := vword v[(leftSource 6 k).val] e-vword v[(rightSource 6 k).val] e))
    rw [fastMulWord_int]
    refine ⟨hb.1,hb.2,?_⟩
    rw [fastMul_field,stageValues_word _ _ _ _ he,
      ite_eq_right (fun h => hk ((final_sides k).1.mp h)),ite_eq_left ((final_sides k).2.mpr hk),
      fastMulWord_int,fastMul_field]
    change _*ofInt (finalZ 6 0)=_
    rw [folded_root_field,Fin.mul_assoc]

theorem foldedStage_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : StageBound v 6 268173344) (hf : BankField u v w)
    (k : Fin 8) {e : Nat} (he : e<4) :
    let x := vword (scaleValues (stageValues 6 v (finalZ 6)))[k.val] e;
    -8380417<x.toInt ∧ x.toInt<2*8380417 ∧
      ofInt x.toInt=(InverseTraversal.run (stridedStageOps u 1 6) w)[InverseTraversal.stridedLoc u k.val e]!*ofInt 16382 := by
  have h := folded_lane v k he
  have hs := stridedStageValues_field (6 : Fin 7) v w hu 1 (by decide) (by decide) hv hf k e he
  exact ⟨h.1,h.2.1,h.2.2.trans (congrArg (·*ofInt 16382) hs)⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseFinalBankFieldRun`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def finalIndex (i : Nat) : Nat := if i<4 then 7-i else if i<6 then 3-(i-4) else 1

def stridedRunOps (u i : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => stridedStageOps u (finalIndex i) i ++ stridedRunOps u (i+1) n

theorem finalZ_index {i : Nat} (hi : i<6) : finalZ i=(fun _ => (negZetaNat (finalIndex i) : Int)) := by
  funext e
  simp only [finalZ,finalValue,finalIndex]
  split
  · rfl
  · rfl

theorem runValues_final_six (i n : Nat) (hin : i+n≤6) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (hv : StageBound v i 268173344) (hf : BankField u v w) :
    StageBound (runValues finalZ i n v) (i+n) 268173344 ∧
      BankField u (runValues finalZ i n v) (InverseTraversal.run (stridedRunOps u i n) w) := by
  induction n generalizing i v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hi : i<6 := by omega_using [hin]
    have hp := stageValues_bound ⟨i,by omega_using [hin]⟩ v (finalZ i) (by decide) (by decide) hv
    have hfield := stridedStageValues_field ⟨i,by omega_using [hin]⟩ v w hu (finalIndex i) (by decide) (by decide) hv hf
    rw [← finalZ_index hi] at hfield
    have h := ih (i := i+1) (by omega_using [hin]) _ _ hp hfield
    simpa only [runValues,stridedRunOps,InverseTraversal.run_append,Nat.add_assoc,Nat.add_comm 1 n] using h

theorem stridedOps_eq {u : Nat} (hu : u<8) :
    stridedRunOps u 0 6 ++ stridedStageOps u 1 6=InverseTraversal.stridedSlice u := by
  exact (show ∀ u : Fin 8,
    stridedRunOps u.val 0 6 ++ stridedStageOps u.val 1 6=InverseTraversal.stridedSlice u.val
    by decide +kernel) ⟨u,hu⟩

theorem runValues_split_last (v : Vector (BitVec 128) 8) :
    runValues finalZ 0 7 v=stageValues 6 (runValues finalZ 0 6 v) (finalZ 6) := rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseMemoryFinalField`, which only this module used -/

section

/-! ## From `InverseMemoryFinalValues.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem finalPass_bank_original (m : Mem) (p : Addr) (q : BitVec 128) {u : Nat} (hu : u<8) :
    readBank (finalPassMem m p q u) (coeffAddr p (4*u)) 128=
      readBank m (coeffAddr p (4*u)) 128 := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [readBank_coeff _ p (4*u) 32 ⟨i,hi⟩ he,readBank_coeff _ p (4*u) 32 ⟨i,hi⟩ he]
  exact finalPass_untouched m p q (by omega_using [hu]) (by change 4*u+32*i+e<256; omega_using [hu, hi, he]) (by omega_using [hu, he])

/-- A completed coefficient is the canonical result of its own strided bank,
evaluated on the original pass input. -/
theorem finalPass_processed (m : Mem) (p : Addr) (q : BitVec 128) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hp : k%32/4<u) :
    coeffAt (finalPassMem m p q u) p k=
      vword (finalValues (readBank m (coeffAddr p (4*(k%32/4))) 128) q)[k/32]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [finalPassMem_step]
    by_cases he : k%32/4=u
    · have hi : k/32<8 := by change k<256 at hk; omega_using [hk]
      have hidx : 4*u+32*(k/32)+k%4=k := by omega_using [he]
      have hx := finalMemStep_at (finalPassMem m p q u) p q (by omega_using [hu] : u<8)
        ⟨k/32,hi⟩ (e := k%4) (by omega_using [])
      rw [hidx,finalPass_bank_original m p q (by omega_using [hu])] at hx
      simpa only [he,getElem!_pos (finalValues (readBank m (coeffAddr p (4*u)) 128) q) (k/32) hi] using hx
    · rw [finalMemStep_outside _ _ _ (by omega_using [hu]) hk he]
      exact ih (by omega_using [hu]) (by omega_using [hp, he])

theorem finalPass_all_values (m : Mem) (p : Addr) (q : BitVec 128) {k : Nat} (hk : k<n) :
    coeffAt (finalPassMem m p q 8) p k=
      vword (finalValues (readBank m (coeffAddr p (4*(k%32/4))) 128) q)[k/32]! (k%4) :=
  finalPass_processed m p q (by decide) hk (by omega_using [])

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseMemoryFinalField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Canonical bank outputs with folded scaling establish the complete final
memory pass's field result, independently of the order of disjoint slices. -/
theorem finalPass_field_of_banks {m : Mem} {p : Addr} {qv : BitVec 128} {w : Poly}
    (hb : ∀ u<8, ∀ i : Fin 8, ∀ e<4,
      (vword (finalValues (readBank m (coeffAddr p (4*u)) 128) qv)[i.val] e).toNat<q)
    (hv : ∀ u<8, ∀ i : Fin 8, ∀ e<4,
      ofInt (vword (finalValues (readBank m (coeffAddr p (4*u)) 128) qv)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382) :
    PolyIs (finalPassMem m p qv 8) p ((InverseTraversal.run InverseTraversal.stridedSchedule w).map (· * 16382)) := by
  have hout (k : Nat) (hk : k<n) :
      (coeffAt (finalPassMem m p qv 8) p k).toNat<q ∧
      ofInt (coeffAt (finalPassMem m p qv 8) p k).toInt=
        (InverseTraversal.run InverseTraversal.stridedSchedule w)[k]! * 16382 := by
    have hi : k/32<8 := by change k<256 at hk; omega_using [hk]
    have hu : k%32/4<8 := by omega_using []
    have he : k%4<4 := by omega_using []
    rw [finalPass_all_values m p qv hk,getElem!_pos (finalValues (readBank m (coeffAddr p (4*(k%32/4))) 128) qv) (k/32) hi]
    refine ⟨hb _ hu ⟨k/32,hi⟩ _ he,?_⟩
    have hh := hv _ hu ⟨k/32,hi⟩ _ he
    have hidx : 4*(k%32/4)+32*(k/32)+k%4=k := by omega_using []
    rw [hidx] at hh
    rw [InverseTraversal.strided_coordinate w hk]
    exact hh
  refine ⟨fun k hk => (hout k hk).1,ext_getElem! fun k hk => ?_⟩
  rw [polyAt_get _ _ hk,map_mul_get _ _ hk]
  have hh := hout k hk
  have hint : (coeffAt (finalPassMem m p qv 8) p k).toInt=
      ((coeffAt (finalPassMem m p qv 8) p k).toNat : Int) := by
    apply BitVec.toInt_eq_toNat_of_lt
    have hq : q=8380417 := rfl
    omega
  rw [hint,ofInt_nat_eq] at hh
  exact hh.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


/-! ## From `InverseFinalBankFieldCanonical.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa

/-- The final store's existing correction preserves each field value and
produces its canonical representative, given the strict Barrett range. -/
theorem canonicalValues_lane (v : Vector (BitVec 128) 8) (qv : BitVec 128)
    (i : Fin 8) {e : Nat} (he : e<4) (hq : vword qv e=8380417#32)
    (hl : -8380417<(vword v[i.val] e).toInt)
    (hh : (vword v[i.val] e).toInt<2*8380417) :
    (vword (canonicalValues v qv)[i.val] e).toNat<8380417 ∧
      ofInt (vword (canonicalValues v qv)[i.val] e).toInt=ofInt (vword v[i.val] e).toInt := by
  simp only [canonicalValues,Vector.getElem_ofFn]
  rw [canonicalVector_word _ _ he hq]
  exact ⟨canonicalWord_bounds _ hl hh,canonicalWord_field _ hl hh⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseMemoryField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Lift a resident local bank's arithmetic result into the global polynomial
invariant, preserving all coefficients outside that bank. -/
theorem firstMemStep_field {m : Mem} {p : Addr} {w : Poly} {u : Nat} {bound : Int}
    (hu : u<8) (h : SignedPolyIs m p w (-bound) bound)
    (hb : ∀ i : Fin 8, ∀ e<4,
      -bound≤(vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt ∧
      (vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt≤bound)
    (hv : ∀ i : Fin 8, ∀ e<4,
      ofInt (vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.localSlice u) w)[32*u+4*i.val+e]!) :
    SignedPolyIs (firstMemStep m p u) p
      (InverseTraversal.run (InverseTraversal.localSlice u) w) (-bound) bound := by
  constructor
  · intro k hk
    by_cases hs : k/32=u
    · have hi : (k%32)/4<8 := by omega_using []
      have he : 32*u+4*((k%32)/4)+k%4=k := by omega_using [hs]
      have hx := firstMemStep_at m p hu ⟨(k%32)/4,hi⟩ (e := k%4) (by omega_using [])
      rw [he] at hx
      rw [hx]
      exact hb ⟨(k%32)/4,hi⟩ _ (by omega_using [])
    · rw [firstMemStep_outside m p hu hk (by omega_using [hs])]
      exact h.bound k hk
  · intro k hk
    by_cases hs : k/32=u
    · have hi : (k%32)/4<8 := by omega_using []
      have he : 32*u+4*((k%32)/4)+k%4=k := by omega_using [hs]
      have hx := firstMemStep_at m p hu ⟨(k%32)/4,hi⟩ (e := k%4) (by omega_using [])
      rw [he] at hx
      rw [hx]
      simpa only [he] using hv ⟨(k%32)/4,hi⟩ (k%4) (by omega_using [])
    · rw [firstMemStep_outside m p hu hk (by omega_using [hs]),h.value k hk,
        InverseTraversal.run_outside _ _ _ (InverseTraversal.local_supported ⟨u,hu⟩) w hk hs]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseMemoryFirstPass.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem firstPass_field_prefix {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) {u : Nat} (hu : u≤8) :
    SignedPolyIs (firstPassMem m p u) p
      (InverseTraversal.run ((List.range u).flatMap InverseTraversal.localSlice) w)
      (-268173344) 268173344 := by
  induction u with
  | zero => exact h.mono (by decide) (by decide)
  | succ u ih =>
    have hp := ih (by omega_using [hu])
    have hf : InnerBankField u
        (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)
        (InverseTraversal.run ((List.range u).flatMap InverseTraversal.localSlice) w) := by
      intro i e he
      rw [readBank_coeff _ p (32*u) 4 i he]
      exact hp.value _ (by change 32*u+4*i.val+e<256; omega_using [hu, he])
    have hb : BankBound (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16) 8380417 :=
      fun i e he => firstPass_bank_bound (by omega_using [hu]) h.bound i he
    have hs := fiveValues_field _ _ (by omega_using [hu] : u<8) hb hf
    have hm := firstMemStep_field (by omega_using [hu] : u<8) hp hs.1 hs.2
    simpa only [firstPassMem_step,List.range_succ,List.flatMap_append,
      List.flatMap_singleton,InverseTraversal.run_append] using hm

/-- All eight local blocks implement the first five inverse layers, retaining
bounded signed representatives for the subsequent strided pass. -/
theorem firstPass_field {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) :
    SignedPolyIs (firstPassMem m p 8) p
      (InverseTraversal.run InverseTraversal.localSchedule w) (-268173344) 268173344 :=
  firstPass_field_prefix h (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseFinalBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The selected strided final pass returns canonical coefficients and applies
exactly the last three inverse layers with the folded Montgomery scale. -/
theorem finalValues_field (v : Vector (BitVec 128) 8) (qv : BitVec 128) (w : Poly)
    {u : Nat} (hu : u<8) (hv : BankBound v 268173344) (hf : BankField u v w)
    (hq : ∀ e<4, vword qv e=8380417#32) (i : Fin 8) {e : Nat} (he : e<4) :
    (vword (finalValues v qv)[i.val] e).toNat<8380417 ∧
      ofInt (vword (finalValues v qv)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382 := by
  have hp := runValues_final_six 0 6 (by decide) v w hu
    ((stageBound_zero v 268173344).mpr hv) hf
  have hl := foldedStage_field _ _ hu hp.1 hp.2 i he
  have hc := canonicalValues_lane _ qv i he (hq e he) hl.1 hl.2.1
  rw [finalValues,runValues_split_last]
  refine ⟨hc.1,hc.2.trans ?_⟩
  simpa only [← InverseTraversal.run_append,stridedOps_eq hu,
    InverseTraversal.stridedLoc,show 32*i.val+4*u+e=4*u+32*i.val+e by omega_using [],
    show ofInt (16382 : Int)=(16382 : Zq) by decide +kernel] using hl.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseMemoryCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem finalPass_field {m : Mem} {p : Addr} {w : Poly} {qv : BitVec 128}
    (h : SignedPolyIs m p w (-268173344) 268173344)
    (hq : ∀ e<4, vword qv e=8380417#32) :
    PolyIs (finalPassMem m p qv 8) p ((InverseTraversal.run InverseTraversal.stridedSchedule w).map (· * 16382)) := by
  have bank (u : Nat) (hu : u<8) := fun (i : Fin 8) (e : Nat) (he : e<4) =>
    finalValues_field (readBank m (coeffAddr p (4*u)) 128) qv w hu
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        exact h.bound _ (by change 4*u+32*j.val+e<256; omega_using [hu, he]))
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          h.value (4*u+32*j.val+e) (by change 4*u+32*j.val+e<256; omega_using [hu, he])) hq i he
  exact finalPass_field_of_banks (fun u hu i e he => (bank u hu i e he).1)
    (fun u hu i e he => (bank u hu i e he).2)

/-- Exact selected two-pass inverse, valid also for centered raw products. -/
theorem inverseMem_field_signed {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) :
    PolyIs (inverseMem m p) p (montgomeryNttInv w) := by
  have hp := finalPass_field (firstPass_field h) (qv := HighPack.repeatedWord 8380417)
    (fun e he => HighPack.repeatedWord_lane _ he)
  simpa only [inverseMem,InverseTraversal.traversal_montgomery] using hp

theorem inverseMem_field {m : Mem} {p : Addr} {w : Poly} (h : PolyIs m p w) :
    PolyIs (inverseMem m p) p (montgomeryNttInv w) := by
  apply inverseMem_field_signed
  constructor
  · intro k hk
    rw [VG.Proof.MlDsa.AArch64.Optimized.canonicalWord_int _ (h.1 k hk)]
    have hb := h.1 k hk
    change (coeffAt m p k).toNat<8380417 at hb
    omega_using [hb]
  · intro k hk
    rw [VG.Proof.MlDsa.AArch64.Optimized.canonicalWord_field _ (h.1 k hk),← polyAt_get _ _ hk,h.2]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
