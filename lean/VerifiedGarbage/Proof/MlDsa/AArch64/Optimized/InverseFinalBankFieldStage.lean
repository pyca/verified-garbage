module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldStage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

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
