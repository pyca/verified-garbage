import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalField
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt

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
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]
  | succ t ih =>
    rw [stridedRegBlock,foldl_range_succ]
    change (blockN bflyInv (stridedRegBlock w base gap u z t) (32*gap) z (stridedLoc u (base+t) 0) 4)[stridedLoc u i e]! = _
    rw [blockN_bflyInv_get' _ (by omega) (by omega) (by unfold stridedLoc n; omega) (by unfold stridedLoc n; omega)]
    by_cases ha : i=base+t
    · subst i
      rw [ite_eq_left (by unfold stridedLoc; omega),
        show stridedLoc u (base+t) e+32*gap=stridedLoc u (base+t+gap) e by unfold stridedLoc; omega,
        ih (by omega) hi, ih (by omega) (by omega)]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · by_cases hd : i=base+t+gap
      · subst i
        rw [ite_eq_right (by unfold stridedLoc; omega),ite_eq_left (by unfold stridedLoc; omega),
          show stridedLoc u (base+t+gap) e-32*gap=stridedLoc u (base+t) e by unfold stridedLoc; omega,
          ih (by omega) hi,ih (by omega) (by omega)]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
        rw [Nat.add_sub_cancel]
      · rw [ite_eq_right (by unfold stridedLoc; omega),ite_eq_right (by unfold stridedLoc; omega),ih (by omega) hi]
        have h1 : (base≤i ∧ i<base+t) ↔ (base≤i ∧ i<base+(t+1)) := by omega
        have h2 : (base+gap≤i ∧ i<base+gap+t) ↔ (base+gap≤i ∧ i<base+gap+(t+1)) := by omega
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
