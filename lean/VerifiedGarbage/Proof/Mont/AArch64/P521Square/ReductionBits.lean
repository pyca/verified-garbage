module
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Spec.Weierstrass


@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Square

theorem orHigh9 (x : Word) :
    x ||| (BitVec.ofNat 64 (2^64-1) <<< 9) =
      (BitVec.ofNat 55 (2^55-1) ++ x.setWidth 9) := by
  change x ||| (BitVec.allOnes 64 <<< 9) = BitVec.allOnes 55 ++ x.setWidth 9
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_append]
  by_cases h : i < 9
  · simp only [hi, h, decide_true, Bool.not_true, Bool.true_and, Bool.and_false,
      Bool.false_and, Bool.or_false, ite_true]
  · have hi55 : i - 9 < 55 := by omega
    have hi64 : i - 9 < 64 := by omega
    simp only [hi, h, hi55, hi64, decide_true, decide_false, Bool.not_false,
      Bool.and_true, Bool.or_true, ite_false]

theorem orHigh9_value (x : Word) :
    (x ||| (BitVec.ofNat 64 (2^64-1) <<< 9)).toNat = x.toNat % 512 + (2^64-512) := by
  rw [orHigh9, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (x.setWidth 9).isLt]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega

theorem mask9 (x : Word) : x &&& BitVec.ofNat 64 511 = (x.setWidth 9).setWidth 64 := by
  change x &&& (BitVec.allOnes 9).setWidth 64 = (x.setWidth 9).setWidth 64
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hi, decide_true, Bool.true_and, Bool.and_comm]

theorem mask9_value (x : Word) : (x &&& BitVec.ofNat 64 511).toNat = x.toNat % 512 := by
  rw [mask9]
  simp only [BitVec.toNat_setWidth]
  omega

end VG.Proof.Mont.AArch64.P521Square
