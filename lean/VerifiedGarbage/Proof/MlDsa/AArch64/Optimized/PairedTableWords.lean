import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

 theorem tailRoot_lt (j : Nat) : tailRoot j < 8380417 := by
  unfold tailRoot
  split
  · decide
  · split
    · exact Nat.mod_lt _ (by decide)
    · exact Nat.mod_lt _ (by decide)

theorem tailValue_lt (p : Nat × Bool) : tailValue p < 2^32 := by
  have hz := tailRoot_lt p.1
  have hb : tailRoot p.1*2^31/8380417 < 2^31 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).2
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hz (show 0<2^31 by decide)
  cases h : p.2 <;> simp only [tailValue,bar,h,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem expandedVals_lt {i : Nat} (hi : i<1024) : expandedVals[i]! < 2^32 := by
  by_cases h : i<960
  · rw [expanded_first h]; exact InverseTable.expandedVals_lt (by omega)
  · rw [show i=960+(i-960) by omega,expanded_tail (by omega)]
    exact tailValue_lt _

theorem expandedWords_length : expandedWords.length = 512 := by
  simp only [expandedWords,List.length_map,List.length_range,expandedVals_length]

private theorem range_map_get {α : Type} [Inhabited α] (f : Nat → α) {n i : Nat}
    (hi : i<n) : ((List.range n).map f)[i]! = f i := by
  rw [getElem!_pos ((List.range n).map f) i (by simpa only [List.length_map,List.length_range] using hi),
    List.getElem_map,List.getElem_range]

theorem expandedWords_get {i : Nat} (hi : i<512) :
    expandedWords[i]! = BitVec.ofNat 64 (expandedVals[2*i]!+2^32*expandedVals[2*i+1]!) := by
  exact range_map_get _ (by simpa only [expandedVals_length] using hi)

theorem expandedWords_low {i : Nat} (hi : i<512) :
    (expandedWords[i]!).extractLsb' 0 32 = BitVec.ofNat 32 expandedVals[2*i]! := by
  rw [expandedWords_get hi]
  exact TableConstants.pack_low _ _ (expandedVals_lt (by omega)) (expandedVals_lt (by omega))

theorem expandedWords_high {i : Nat} (hi : i<512) :
    (expandedWords[i]!).extractLsb' 32 32 = BitVec.ofNat 32 expandedVals[2*i+1]! := by
  rw [expandedWords_get hi]
  exact TableConstants.pack_high _ _ (expandedVals_lt (by omega)) (expandedVals_lt (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable
