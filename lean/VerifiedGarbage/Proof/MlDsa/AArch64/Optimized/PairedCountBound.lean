import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassCount
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCount

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem checkOutput_bit (raw low high : BitVec 128) (c : CheckConstants)
    {e : Nat} (he : e<4) : (vword (checkOutput true raw low high c) e).toNat≤1 := by
  simp only [checkOutput,ite_true,laneVector_word _ he]
  exact hintWord_bit _ _ _

/-- A bounded list of bits has an exact natural sum in its 32-bit accumulator. -/
theorem bitSum_value (xs : List (BitVec 32)) (hl : xs.length≤128)
    (hb : ∀x∈xs,x.toNat≤1) :
    xs.sum.toNat=(xs.map BitVec.toNat).sum ∧ xs.sum.toNat≤xs.length := by
  induction xs with
  | nil => exact ⟨rfl,Nat.le_refl _⟩
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (by simp only [List.length_cons] at hl; omega)
      (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    have hn : x.toNat+xs.sum.toNat<2^32 := by simp only [List.length_cons] at hl; omega
    simp only [List.sum_cons,List.map_cons,BitVec.toNat_add,Nat.mod_eq_of_lt hn]
    exact ⟨by rw [ht.1],by simp only [List.length_cons]; omega⟩

theorem hintSum_bound (v : Values) (out aux : Addr) (c : CheckConstants) (m : Mem)
    {e : Nat} (he : e<4) : (hintSum v out aux c m e allChecks).toNat≤16 := by
  unfold hintSum
  have h := bitSum_value
    (allChecks.map fun i => vword (checkOutput true ((v i.1)[i.2.val])
      (m.read (checkAddr out i) 16) (m.read (checkAddr aux i) 16) c) e)
    (by rw [List.length_map]; decide)
    (by intro x hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact checkOutput_bit _ _ _ _ he)
  exact h.2

/-- Eight paired slices accumulate at most 128 hints in each SIMD lane. -/
theorem passHintSum_bound (work out aux : Addr) (c : CheckConstants) (m : Mem)
    {e n : Nat} (he : e<4) (hn : n≤8) :
    (passHintSum work out aux c m e n).toNat≤16*n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hp := ih (by omega)
    have hs := hintSum_bound
      (fun p => Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*n)) 128 p))
      (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c m he
    rw [passHintSum,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
    omega

end VG.Proof.MlDsa.AArch64.Optimized.Paired
