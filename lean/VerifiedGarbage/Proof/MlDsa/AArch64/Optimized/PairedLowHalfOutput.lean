import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowInputFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowHalfValue (v : Values) (i : LowIndex) (h : Fin 2) : BitVec 128 :=
  (v i.1)[2*i.2.val+h.val]

/-- Each half of a paired step writes its exact high result. -/
theorem lowPair_read_high (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr out i h) 16=lowHighOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) := by
  have hd0 (h : Fin 2) := hd.sep (lowAddr_contains_base out i h) (lowAddr_contains_base aux i 0)
  have hd1 (h : Fin 2) := hd.sep (lowAddr_contains_base out i h) (lowAddr_contains_base aux i 1)
  fin_cases h
  · exact lowPair_read_high0 _ _ _ _ _ _ _ _ _
      (lowAddr_sep out (h:=0) (k:=1) (Or.inr (by decide))) (hd0 0) (hd1 0)
  · exact lowPair_read_high1 _ _ _ _ _ _ _ _ _ (hd0 1) (hd1 1)

/-- Each half also writes its exact signed low result, including rejected paths. -/
theorem lowPair_read_low (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (i : LowIndex) (h : Fin 2) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr aux i h) 16=lowLowOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) c := by
  fin_cases h
  · exact lowPair_read_low0 _ _ _ _ _ _ _ _ _ (lowAddr_sep aux (h:=0) (k:=1) (Or.inr (by decide)))
  · exact lowPair_read_low1 _ _ _ _ _ _ _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired
