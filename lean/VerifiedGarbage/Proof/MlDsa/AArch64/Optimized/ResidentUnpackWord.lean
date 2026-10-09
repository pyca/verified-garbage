import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackIndex
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

private theorem toInt32 (x : BitVec 32) :
    x.toInt = if x.toNat < 2147483648 then (x.toNat : Int) else (x.toNat : Int)-4294967296 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> first | rfl | omega

theorem signMask32 (d : BitVec 32) : d.sshiftRight 31 = if d.toNat < 2^31 then 0 else -1 := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight,toInt32]
  have := d.isLt
  split
  · rw [show (0 : BitVec 32).toInt=0 by decide,Int.shiftRight_eq_div_pow]; omega
  · rw [show (-1 : BitVec 32).toInt= -1 by decide,Int.shiftRight_eq_div_pow]; omega

/-- Canonical coefficient correction used by the vector parser. -/
def unpackWord (b x : BitVec 32) : BitVec 32 :=
  let r := b-x
  r + (r.sshiftRight 31 &&& 8380417#32)

theorem unpackWord_toNat {b x : BitVec 32} (hb : b.toNat < 8380417) (hx : x.toNat < 8380417) :
    (unpackWord b x).toNat = (b.toNat+8380417-x.toNat)%8380417 := by
  dsimp only [unpackWord]
  by_cases h : b.toNat < x.toNat
  · have hs : (b-x).sshiftRight 31=0xffffffff#32 := by rw [signMask32,ite_eq_right (by bv_omega)]; rfl
    rw [hs,show (0xffffffff#32 &&& 8380417#32)=8380417#32 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    bv_omega
  · have hs : (b-x).sshiftRight 31=0#32 := by rw [signMask32,ite_eq_left (by bv_omega)]; rfl
    rw [hs,show (0#32 &&& 8380417#32)=0#32 from rfl]
    have he : (b.toNat+8380417-x.toNat)%8380417=b.toNat-x.toNat := by omega
    rw [he]
    bv_omega

/-- Uniform vector shifts recover the width-specific packed field. Only the
low field bits are observed, so no extra assumption on the input word is needed. -/
theorem align_field (x : BitVec 32) {d e : Nat} (hd : d=18 ∨ d=20) :
    (((x <<< ((if d=20 then 4 else 6)-d*e%8)) >>> (if d=20 then 4 else 6)) &&&
      BitVec.ofNat 32 (2^d-1)) = (x.extractLsb' (d*e%8) d).setWidth 32 := by
  have hb := fieldShift_bounds (g := 0) (e := e) hd
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat,BitVec.getLsbD_setWidth,BitVec.getLsbD_extractLsb',
    Nat.testBit_two_pow_sub_one]
  by_cases hl : i < d
  · rcases hd with rfl | rfl <;>
      simp only [ite_true,ite_eq_right (by decide : ¬ (18:Nat)=20)] at *
    all_goals
      simp (disch := omega) only [decide_eq_true,decide_eq_false,Bool.true_and,Bool.and_true,
        Bool.not_false]
      congr 1
      omega
  · rcases hd with rfl | rfl <;>
      simp only [ite_true,ite_eq_right (by decide : ¬ (18:Nat)=20)] at *
    all_goals simp (disch := omega) only [decide_eq_true,decide_eq_false,Bool.false_and,Bool.and_false]

/-- The SIMD multiplier is a power of two, hence exactly the proven alignment
shift rather than an approximate numeric operation. -/
theorem align_mul_field (x : BitVec 32) {d e : Nat} (hd : d=18 ∨ d=20) :
    (((x * BitVec.ofNat 32 (2^((if d=20 then 4 else 6)-d*e%8))) >>>
      (if d=20 then 4 else 6)) &&& BitVec.ofNat 32 (2^d-1)) =
      (x.extractLsb' (d*e%8) d).setWidth 32 := by
  have hp (k : Nat) : BitVec.ofNat 32 (2^k)=BitVec.twoPow 32 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat,BitVec.toNat_twoPow]
  rw [hp,← BitVec.shiftLeft_eq_mul_twoPow]
  exact align_field x hd

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
