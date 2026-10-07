import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSubtract
import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Impl.Weierstrass.AArch64.FastNaf

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519 VG.Proof.Ed25519.AArch64

theorem fastMagnitude_bound (w k j : Nat) : FastNaf.magnitude w k j≤63 := by
  by_cases h7 : w=7
  · simpa only [FastNaf.magnitude,h7,ite_true] using FastNaf7.magnitude_le k j
  · have h := Naf5.magnitude_le k j
    simp only [FastNaf.magnitude,h7,ite_false]
    omega

theorem fastDigit_eq (w k j : Nat) : FastNaf.digit w k j=
    if FastNaf.negative w k j then -(FastNaf.magnitude w k j:Int) else (FastNaf.magnitude w k j:Int) := by
  by_cases h7 : w=7 <;> simp only [FastNaf.digit,FastNaf.negative,FastNaf.magnitude,h7,ite_true,ite_false,Naf5.digit,FastNaf7.digit]

theorem fastWord_toNat (w k j : Nat) :
    (BitVec.ofInt 64 (FastNaf.digit w k j)).toNat =
      if FastNaf.negative w k j then 2^64-FastNaf.magnitude w k j else FastNaf.magnitude w k j := by
  have hb := fastMagnitude_bound w k j
  simp only [fastDigit_eq,BitVec.toNat_ofInt]
  cases hn : FastNaf.negative w k j
  · simp only [Bool.false_eq_true,ite_false]
    change ((FastNaf.magnitude w k j:Int)%18446744073709551616).toNat=_
    omega
  · have hp := FastNaf.negative_magnitude_pos w k j hn
    simp only [ite_true]
    change ((-(FastNaf.magnitude w k j:Int))%18446744073709551616).toNat=_
    omega

theorem fastSign_toNat (w k j : Nat) :
    (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)).toNat =
      if FastNaf.negative w k j then 2^64-1 else 0 := by
  have hb := fastMagnitude_bound w k j
  have hp := FastNaf.negative_magnitude_pos w k j
  simp only [BitVec.toNat_sub,BitVec.toNat_zero,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,fastWord_toNat]
  cases hn : FastNaf.negative w k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := hp hn
    simp only [ite_true]; omega

theorem fastSub5_next (a b c d e : BitVec 64) (w k j : Nat)
    (hv : nafVal5 a b c d e=FastNaf.residual w k j) (hb : FastNaf.residual w k j≤2^256) :
    let x := BitVec.ofInt 64 (FastNaf.digit w k j)
    let out := nafSub5 a b c d e x (0#64-(x>>>63))
    nafVal5 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2 = 2*FastNaf.residual w k (j+1) := by
  have hs := nafSub5_value a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j))
    (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
  have hlt := nafVal5_lt (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j))
    (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).1
    (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).2.2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).2.2.2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).2.2.2.2
  dsimp only at hs ⊢
  rw [hv] at hs
  have he : nafVal5 (BitVec.ofInt 64 (FastNaf.digit w k j))
      (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
      (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
      (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
      (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)) =
      if FastNaf.negative w k j then 2^320-FastNaf.magnitude w k j else FastNaf.magnitude w k j := by
    simp only [nafVal5,fastWord_toNat,fastSign_toNat]
    cases hn : FastNaf.negative w k j <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · omega
    · have := fastMagnitude_bound w k j; omega
  rw [he] at hs
  have hr := FastNaf.recurrence w k j
  have hm := fastMagnitude_bound w k j
  cases hn : FastNaf.negative w k j <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true] at hs hr <;> omega

/-- Five adjacent extract-right instructions implement a whole-number shift. -/
theorem fastShift5_value (a b c d e : BitVec 64) :
    nafVal5 ((b++a).extractLsb' 5 64) ((c++b).extractLsb' 5 64)
      ((d++c).extractLsb' 5 64) ((e++d).extractLsb' 5 64) (e>>>5) = nafVal5 a b c d e/32 := by
  have extr (hi lo : BitVec 64) : ((hi++lo).extractLsb' 5 64).toNat = lo.toNat/32+2^59*(hi.toNat%32) := by
    rw [BitVec.extractLsb'_toNat,BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
      Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    have := hi.isLt; have := lo.isLt
    omega
  simp only [nafVal5,extr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega

/-- Five adjacent extract-right instructions implement a whole-number shift. -/
theorem fastShift7_value (a b c d e : BitVec 64) :
    nafVal5 ((b++a).extractLsb' 7 64) ((c++b).extractLsb' 7 64)
      ((d++c).extractLsb' 7 64) ((e++d).extractLsb' 7 64) (e>>>7) = nafVal5 a b c d e/128 := by
  have extr (hi lo : BitVec 64) : ((hi++lo).extractLsb' 7 64).toNat = lo.toNat/128+2^57*(hi.toNat%128) := by
    rw [BitVec.extractLsb'_toNat,BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
      Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    have := hi.isLt; have := lo.isLt
    omega
  simp only [nafVal5,extr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega

theorem fastShift_value (w : Nat) (hw : w=1 ∨ w=5 ∨ w=7) (a b c d e : BitVec 64) :
    nafVal5 ((b++a).extractLsb' w 64) ((c++b).extractLsb' w 64)
      ((d++c).extractLsb' w 64) ((e++d).extractLsb' w 64) (e>>>w) = nafVal5 a b c d e/2^w := by
  rcases hw with rfl | rfl | rfl
  · exact nafShift5_value ..
  · exact fastShift5_value ..
  · exact fastShift7_value ..


end VG.Proof.Weierstrass.AArch64
