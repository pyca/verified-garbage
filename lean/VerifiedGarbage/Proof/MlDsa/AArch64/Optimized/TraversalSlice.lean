import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem blockPrefix_get (w : Poly) {len : Nat} {z : Zq} {start t : Nat} (hlen : 0 < len) (ht : t ≤ len)
    (hs : start + len + t ≤ n) {i : Nat} (hi : i < n) :
    (blockN bfly w len z start t)[i]! =
      if start ≤ i ∧ i < start + t then w[i]! + z * w[i + len]!
      else if start + len ≤ i ∧ i < start + len + t then w[i - len]! - z * w[i]!
      else w[i]! := by
  induction t generalizing i with
  | zero =>
    rw [blockN_zero, ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ t ih =>
    rw [blockN_succ, bfly_get _ hlen (by omega) _ hi, ih (i := start + t) (by omega) (by omega) (by omega),
      ih (i := start + t + len) (by omega) (by omega) (by omega), ih (by omega) (by omega) hi]
    rcases (by omega : i < start ∨ (start ≤ i ∧ i < start + t) ∨ i = start + t ∨
        (start + t < i ∧ i < start + len) ∨ (start + len ≤ i ∧ i < start + t + len) ∨
        i = start + t + len ∨ start + t + len < i) with h | h | rfl | h | h | rfl | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_cancel, ↓reduceIte]


def loc (u i e : Nat) : Nat := 32*i+4*u+e

def regBlock (w : Poly) (base gap u : Nat) (z : Zq) (t : Nat) : Poly :=
  (List.range t).foldl (fun w j => blockN bfly w (32*gap) z (loc u (base+j) 0) 4) w

/-- A register group's first t butterflies update exactly its selected register
pairs, independently in each of the four lanes. -/
theorem regBlock_get (w : Poly) {base gap u t : Nat} (hgap : 0<gap)
    (hb : base+2*gap≤8) (hu : u<8) (ht : t≤gap) (z : Zq)
    {i e : Nat} (hi : i<8) (he : e<4) :
    (regBlock w base gap u z t)[loc u i e]! =
      if base≤i ∧ i<base+t then w[loc u i e]! + z*w[loc u (i+gap) e]!
      else if base+gap≤i ∧ i<base+gap+t then w[loc u (i-gap) e]! - z*w[loc u i e]!
      else w[loc u i e]! := by
  induction t generalizing i with
  | zero =>
    simp only [regBlock,List.range_zero,List.foldl_nil,Nat.add_zero]
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]
  | succ t ih =>
    rw [regBlock,foldl_range_succ]
    change (blockN bfly (regBlock w base gap u z t) (32*gap) z (loc u (base+t) 0) 4)[loc u i e]! = _
    rw [blockPrefix_get _ (by omega) (by omega) (by unfold loc n; omega) (by unfold loc n; omega)]
    by_cases ha : i=base+t
    · subst i
      rw [ite_eq_left (by unfold loc; omega),
        show loc u (base+t) e+32*gap=loc u (base+t+gap) e by unfold loc; omega,
        ih (by omega) hi, ih (by omega) (by omega)]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · by_cases hd : i=base+t+gap
      · subst i
        rw [ite_eq_right (by unfold loc; omega),ite_eq_left (by unfold loc; omega),
          show loc u (base+t+gap) e-32*gap=loc u (base+t) e by unfold loc; omega,
          ih (by omega) hi,ih (by omega) (by omega)]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
        rw [Nat.add_sub_cancel]
      · rw [ite_eq_right (by unfold loc; omega),ite_eq_right (by unfold loc; omega),ih (by omega) hi]
        have h1 : (base≤i ∧ i<base+t) ↔ (base≤i ∧ i<base+(t+1)) := by omega
        have h2 : (base+gap≤i ∧ i<base+gap+t) ↔ (base+gap≤i ∧ i<base+gap+(t+1)) := by omega
        simp only [h1,h2]

def regGroupSchedule (u base gap rootIndex : Nat) : List Op :=
  (List.range gap).flatMap fun j => (List.range 4).map fun e =>
    ⟨loc u (base+j) e,32*gap,rootIndex⟩

theorem run_regGroup (w : Poly) (u base gap rootIndex : Nat) :
    run (regGroupSchedule u base gap rootIndex) w=
      regBlock w base gap u (zetas rootIndex) gap := by
  unfold run regGroupSchedule regBlock
  rw [List.foldl_flatMap]
  apply congrArg (fun f => (List.range gap).foldl f w)
  funext p j
  rw [List.foldl_map]
  unfold blockN
  rw [List.range'_eq_map_range,List.foldl_map]
  apply congrArg (fun f => (List.range 4).foldl f p)
  funext p e
  change bfly p (loc u (base+j) e) (32*gap) (zetas rootIndex)=
    bfly p (loc u (base+j) 0+e) (32*gap) (zetas rootIndex)
  rw [loc,loc,Nat.add_zero]

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
