import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableConstants

namespace VG.Proof.MlDsa.AArch64.Optimized.TableConstants
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem value_lt (p : Nat × Bool) : value p < 2^32 := by
  have hz : zetaTab p.1 < 8380417 := Nat.mod_lt _ (by decide)
  have hb : zetaTab p.1*2^31/8380417 < 2^31 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).2
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hz (show 0<2^31 by decide)
  cases h : p.2 <;> simp only [value,h,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem expandedVals_lt {i : Nat} (hi : i<976) : expandedVals[i]! < 2^32 := by
  rw [expanded_get hi]
  exact value_lt _

theorem pack_low (a b : Nat) (ha : a<2^32) (hb : b<2^32) :
    (BitVec.ofNat 64 (a+2^32*b)).extractLsb' 0 32 = BitVec.ofNat 32 a := by
  have hab : a+2^32*b < 2^64 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hab,
    Nat.shiftRight_zero,Nat.mod_eq_of_lt ha]
  omega

theorem pack_high (a b : Nat) (ha : a<2^32) (hb : b<2^32) :
    (BitVec.ofNat 64 (a+2^32*b)).extractLsb' 32 32 = BitVec.ofNat 32 b := by
  have hab : a+2^32*b < 2^64 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hab,
    Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt hb]
  omega

theorem staticNttWords_length : staticNttWords.length = 488 := by
  simp only [staticNttWords,List.length_map,List.length_range,expandedVals_length]

private theorem range_map_get {α : Type} [Inhabited α] (f : Nat → α) {n i : Nat}
    (hi : i<n) : ((List.range n).map f)[i]! = f i := by
  rw [getElem!_pos ((List.range n).map f) i (by simpa only [List.length_map,List.length_range] using hi),
    List.getElem_map,List.getElem_range]

theorem staticNttWords_get {i : Nat} (hi : i<488) :
    staticNttWords[i]! = BitVec.ofNat 64 (expandedVals[2*i]!+2^32*expandedVals[2*i+1]!) := by
  exact range_map_get _ (by simpa only [expandedVals_length] using hi)

theorem staticNttWords_low {i : Nat} (hi : i<488) :
    (staticNttWords[i]!).extractLsb' 0 32 = BitVec.ofNat 32 expandedVals[2*i]! := by
  rw [staticNttWords_get hi]
  exact pack_low _ _ (expandedVals_lt (by omega)) (expandedVals_lt (by omega))

theorem staticNttWords_high {i : Nat} (hi : i<488) :
    (staticNttWords[i]!).extractLsb' 32 32 = BitVec.ofNat 32 expandedVals[2*i+1]! := by
  rw [staticNttWords_get hi]
  exact pack_high _ _ (expandedVals_lt (by omega)) (expandedVals_lt (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.TableConstants
