import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed66

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG

theorem nonceWord_value (k : BitVec 64) :
    (nonceWord k).toNat=k.toNat%65536+2031616 := by
  have hx : ((k <<< 48) >>> 48).toNat=k.toNat%65536 := by
    rw [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    change (k.toNat*281474976710656 % (65536*281474976710656))/281474976710656=_
    rw [Nat.mul_mod_mul_right,Nat.mul_div_cancel _ (by decide)]
  rw [nonceWord,BitVec.toNat_add,hx]
  change (k.toNat%65536+2031616)%18446744073709551616=_
  exact Nat.mod_eq_of_lt (by omega)

theorem nonceValue_byte (a k : BitVec 64) (hk : a.toNat=k.toNat%65536+2031616) {i : Nat} (hi : i<8) :
    a.extractLsb' (8*i) 8 =
      if i=0 then k.extractLsb' 0 8 else if i=1 then k.extractLsb' 8 8
      else if i=2 then 0x1f else 0 := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ 3≤i by omega) with h|h|h|h
  · subst i
    simp only [ite_true,Nat.mul_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    rw [hk, Nat.div_one, Nat.add_mod]
    simp only [show 2031616 % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    simpa only [Nat.div_one] using Nat.mod_mul_right_mod k.toNat 256 256
  · subst i
    simp only [ite_eq_right (by decide : ¬ (1:Nat)=0),ite_true,Nat.mul_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    rw [hk]
    change ((k.toNat % (256*256) + 7936*256)/256)%256 = _
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.add_mod]
    simp only [show 7936 % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    rw [Nat.mod_mul_right_div_self, Nat.mod_mod]
  · subst i
    simp only [ite_eq_right (by decide : ¬ (2:Nat)=0),ite_eq_right (by decide : ¬ (2:Nat)=1),ite_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow,Nat.reduceMul]
    rw [hk]
    change ((k.toNat % 65536 + 31*65536)/65536)%256 = 31
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.mod_div_self]
  · simp only [ite_eq_right (by omega : ¬ i=0),ite_eq_right (by omega : ¬ i=1),
      ite_eq_right (by omega : ¬ i=2)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat]
    have hb : 8*i≥24 := by omega
    have he : a.toNat<2^24 := by omega
    have hdiv : a.toNat/2^(8*i)=0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) hb))
    rw [Nat.shiftRight_eq_div_pow,hdiv]
    rfl

theorem nonceWord_byte (k : BitVec 64) {i : Nat} (hi : i<8) :
    (nonceWord k).extractLsb' (8*i) 8 =
      if i=0 then k.extractLsb' 0 8 else if i=1 then k.extractLsb' 8 8
      else if i=2 then 0x1f else 0 :=
  nonceValue_byte (nonceWord k) k (nonceWord_value k) hi

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
