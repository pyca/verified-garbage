import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowSlotLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowFlagValue

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowAddr_contains_base (base : Addr) (i : LowIndex) (h : Fin 2) :
    (⟨base,2048⟩ : Region).Contains (lowAddr base i h) 16 := by
  simp only [lowAddr,lowOff]
  exact Offset.contains_base base (by omega) (by omega)

/-- Both original input vectors of a later pair survive this pair's four stores. -/
theorem lowPair_other_input (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) {i j : LowIndex} (hne : j≠i) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr out j h) 16=d.mem.read (lowAddr out j h) 16 := by
  apply lowPair_read_other
  · simpa only [lowAddr,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using
      lowAddr_sep (h:=h) (k:=0) out (Or.inl hne)
  · simpa only [lowAddr,Fin.val_one,Nat.mul_one] using
      lowAddr_sep (h:=h) (k:=1) out (Or.inl hne)
  · simpa only [lowAddr,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using
      hd.sep (lowAddr_contains_base out j h) (lowAddr_contains_base aux i 0)
  · simpa only [lowAddr,Fin.val_one,Nat.mul_one] using
      hd.sep (lowAddr_contains_base out j h) (lowAddr_contains_base aux i 1)

theorem lowMask_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128)
    (c : LowConstants) (e : Nat) (hm : m'.read out 16=m.read out 16) :
    lowMask g m' out raw c e=lowMask g m out raw c e := by
  simp only [lowMask,lowInputValues,hm]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
