import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTable

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (acceptedIndices)

def nibbleMask (η a b c d : Nat) : Nat :=
 maskOf (decide (a<rbB η)) (decide (b<rbB η)) (decide (c<rbB η)) (decide (d<rbB η))

theorem nibbleMask_lt (η a b c d : Nat) : nibbleMask η a b c d<16 := maskOf_lt _ _ _ _

/-- The table-selected prefix is precisely the old scalar rejection filter. -/
theorem selected_values (η a b c d : Nat) :
    ((acceptedIndices (nibbleMask η a b c d)).map
      (fun i=>ofInt (rbC η ([a,b,c,d][i]!))))=accepted η [a,b,c,d] := by
  unfold nibbleMask
  rw [maskOf_indices]
  simp only [accepted,List.filter_cons,List.filter_nil,List.map_append]
  by_cases ha : a<rbB η <;> by_cases hb : b<rbB η <;>
    by_cases hc : c<rbB η <;> by_cases hd : d<rbB η <;>
    simp [ha,hb,hc,hd]

theorem selected_count (η a b c d : Nat) :
    (acceptedIndices (nibbleMask η a b c d)).length=(accepted η [a,b,c,d]).length := by
  simpa only [List.length_map] using congrArg List.length (selected_values η a b c d)

theorem selected_getD (η a b c d : Nat) {i : Nat}
    (hi : i<(acceptedIndices (nibbleMask η a b c d)).length) :
    ofInt (rbC η ([a,b,c,d][(acceptedIndices (nibbleMask η a b c d))[i]!]!))=
      (accepted η [a,b,c,d]).getD i 0 := by
  rw [←selected_values η a b c d,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa only [List.length_map] using hi),Option.getD_some,
    List.getElem_map,getElem!_pos (acceptedIndices (nibbleMask η a b c d)) i hi]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
