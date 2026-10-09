import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalSlice

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def innerLoc (u i e : Nat) : Nat := 32*u+4*i+e

def innerRegBlock (w : Poly) (base gap u : Nat) (z : Zq) (t : Nat) : Poly :=
  (List.range t).foldl (fun w j => blockN bfly w (4*gap) z (innerLoc u (base+j) 0) 4) w

/-- A register group's first t butterflies update exactly its selected register
pairs, independently in each of the four lanes. -/
theorem innerRegBlock_get (w : Poly) {base gap u t : Nat} (hgap : 0<gap)
    (hb : base+2*gap≤8) (hu : u<8) (ht : t≤gap) (z : Zq)
    {i e : Nat} (hi : i<8) (he : e<4) :
    (innerRegBlock w base gap u z t)[innerLoc u i e]! =
      if base≤i ∧ i<base+t then w[innerLoc u i e]! + z*w[innerLoc u (i+gap) e]!
      else if base+gap≤i ∧ i<base+gap+t then w[innerLoc u (i-gap) e]! - z*w[innerLoc u i e]!
      else w[innerLoc u i e]! := by
  induction t generalizing i with
  | zero =>
    simp only [innerRegBlock,List.range_zero,List.foldl_nil,Nat.add_zero]
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]
  | succ t ih =>
    rw [innerRegBlock,foldl_range_succ]
    change (blockN bfly (innerRegBlock w base gap u z t) (4*gap) z (innerLoc u (base+t) 0) 4)[innerLoc u i e]! = _
    rw [blockPrefix_get _ (by omega) (by omega) (by unfold innerLoc n; omega) (by unfold innerLoc n; omega)]
    by_cases ha : i=base+t
    · subst i
      rw [ite_eq_left (by unfold innerLoc; omega),
        show innerLoc u (base+t) e+4*gap=innerLoc u (base+t+gap) e by unfold innerLoc; omega,
        ih (by omega) hi, ih (by omega) (by omega)]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · by_cases hd : i=base+t+gap
      · subst i
        rw [ite_eq_right (by unfold innerLoc; omega),ite_eq_left (by unfold innerLoc; omega),
          show innerLoc u (base+t+gap) e-4*gap=innerLoc u (base+t) e by unfold innerLoc; omega,
          ih (by omega) hi,ih (by omega) (by omega)]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
        rw [Nat.add_sub_cancel]
      · rw [ite_eq_right (by unfold innerLoc; omega),ite_eq_right (by unfold innerLoc; omega),ih (by omega) hi]
        have h1 : (base≤i ∧ i<base+t) ↔ (base≤i ∧ i<base+(t+1)) := by omega
        have h2 : (base+gap≤i ∧ i<base+gap+t) ↔ (base+gap≤i ∧ i<base+gap+(t+1)) := by omega
        simp only [h1,h2]

def innerRegGroupSchedule (u base gap rootIndex : Nat) : List Op :=
  (List.range gap).flatMap fun j => (List.range 4).map fun e =>
    ⟨innerLoc u (base+j) e,4*gap,rootIndex⟩

theorem run_innerRegGroup (w : Poly) (u base gap rootIndex : Nat) :
    run (innerRegGroupSchedule u base gap rootIndex) w=
      innerRegBlock w base gap u (zetas rootIndex) gap := by
  unfold run innerRegGroupSchedule innerRegBlock
  rw [List.foldl_flatMap]
  apply congrArg (fun f => (List.range gap).foldl f w)
  funext p j
  rw [List.foldl_map]
  unfold blockN
  rw [List.range'_eq_map_range,List.foldl_map]
  apply congrArg (fun f => (List.range 4).foldl f p)
  funext p e
  change bfly p (innerLoc u (base+j) e) (4*gap) (zetas rootIndex)=
    bfly p (innerLoc u (base+j) 0+e) (4*gap) (zetas rootIndex)
  rw [innerLoc,innerLoc,Nat.add_zero]

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
