import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintOrder
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintPacked

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

private theorem fourCount_nat (a b c d : BitVec 32)
    (ha : a.toNat≤128) (hb : b.toNat≤128) (hc : c.toNat≤128) (hd : d.toNat≤128) :
    (a+b+c+d).toNat=a.toNat+b.toNat+c.toNat+d.toNat := by
  simp only [BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]

private theorem pack_success (lo : BitVec 32) (P : Prop) [Decidable P] :
    (lo.setWidth 64 ||| ((if P then (1 : BitVec 64) else 0) <<< 32))=
      BitVec.ofNat 64 (lo.toNat+(if P then 4294967296 else 0)) := by
  apply BitVec.eq_of_toNat_eq
  have hlo := lo.isLt
  by_cases hp : P
  · simp only [ite_eq_left hp]
    change (lo.setWidth 64 ||| ((1#32).setWidth 64 <<< 32)).toNat=_
    rw [packedWords_nat]
    simp only [BitVec.toNat_ofNat,show (1#32).toNat=1 by decide,Nat.one_mul]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [ite_eq_right hp]
    change (lo.setWidth 64 ||| ((0#32).setWidth 64 <<< 32)).toNat=_
    rw [packedWords_nat]
    simp only [BitVec.toNat_ofNat,show (0#32).toNat=0 by decide,Nat.zero_mul]
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem hintFinish_packed (counts flags : BitVec 128) (P : Prop) [Decidable P]
    (hb : ∀e<4,(vword counts e).toNat≤128)
    (hf : finishValue flags=if P then 1 else 0) :
    hintFinishValue counts flags=BitVec.ofNat 64
      (sumN 4 (fun e => (vword counts e).toNat)+(if P then 4294967296 else 0)) := by
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have hs : sumN 4 (fun e => (vword counts e).toNat)=
      (vword counts 0).toNat+(vword counts 1).toNat+(vword counts 2).toNat+(vword counts 3).toNat := by
    exact sumN_four _
  have hsum : (vword counts 0+vword counts 1+vword counts 2+vword counts 3).toNat=
      sumN 4 (fun e => (vword counts e).toNat) := by
    rw [hs]
    exact fourCount_nat _ _ _ _ h0 h1 h2 h3
  unfold hintFinishValue
  rw [hf,pack_success,hsum]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
