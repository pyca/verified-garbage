module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStage
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseArithmetic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerBank
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Arithmetic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttSpec
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly

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
