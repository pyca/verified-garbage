import VerifiedGarbage.Proof.P256.EcdhInverse.Shift
import VerifiedGarbage.Proof.Divstep.Packed20Extract

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep

theorem signed_window (x : BitVec 64) {k : Nat} (hk : k=21 ∨ k=22) :
    (x <<< (43-k)).sshiftRight 43 = (x.extractLsb' k 21).signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight,BitVec.getLsbD_signExtend,
    BitVec.getLsbD_extractLsb',show ¬64≤i by omega,decide_false,
    Bool.not_false,Bool.true_and,hi,decide_true]
  by_cases h : i<21
  · simp only [show 43+i<64 by omega,↓reduceIte,h,
      BitVec.getLsbD_shiftLeft]
    have ha : 43+i-(43-k)=k+i := by omega
    simp only [ha,show ¬43+i<43-k by omega,decide_false,Bool.not_false,
      Bool.true_and,decide_true]
  · simp only [show ¬43+i<64 by omega,↓reduceIte,h,BitVec.msb_eq_getLsbD_last,
      BitVec.getLsbD_shiftLeft,BitVec.getLsbD_extractLsb']
    have ha : 63-(43-k)=k+20 := by omega
    simp only [ha,show ¬63<43-k by omega,decide_false,Bool.not_false,
      Nat.reduceSub,show (64-1:Nat)<64 by decide,show (21-1:Nat)<21 by decide,
      decide_true,Bool.true_and]

theorem signed_window_int (x : Int) {k : Nat} (hk : k=21 ∨ k=22) :
    ((BitVec.ofInt 64 x) <<< (43-k)).sshiftRight 43 =
      BitVec.ofInt 64 (((x/2^k+2^20)%2^21)-2^20) := by
  rw [signed_window _ hk,BitVec.signExtend,BitVec.toInt_extractLsb']
  apply congrArg (BitVec.ofInt 64)
  rw [Nat.shiftRight_eq_div_pow,Int.natCast_ediv,VG.Proof.Divstep.toNat_ofInt64]
  rcases hk with rfl|rfl <;> norm_num [Int.bmod_def] <;> omega

theorem extract_low {n a b : Nat} {u v : Int}
    (hn : n=19 ∨ n=20) (ha : a<2^20) (hb : b<2^20)
    (h : |u|+|v|≤(2:Int)^n) (hu : -(2:Int)^(n-1)≤u) :
    let z := (u*((a:Int)-2^41)+v*((b:Int)-2^62))/2^n
    ((BitVec.ofInt 64 (z+2^20)) <<< (43-(41-n))).sshiftRight 43 =
      BitVec.ofInt 64 (-u) := by
  dsimp only
  rw [signed_window_int _ (by omega),packed20_extract_low hn ha hb h hu]

theorem biased_row_signed {n a b : Nat} {u v : Int}
    (hn : n=19 ∨ n=20) (ha : a<2^20) (hb : b<2^20)
    (h : |u|+|v|≤(2:Int)^n) :
    let z := (u*((a:Int)-2^41)+v*((b:Int)-2^62))/2^n+2^20+2^41;
    -(2:Int)^63≤z ∧ z<2^63 := by
  obtain ⟨hl,hh,hz⟩ := packed20_row hn ha hb h
  have hu := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg v)) h)
  have hv := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg u)) h)
  dsimp only
  rw [hz]
  rcases hn with rfl|rfl <;> norm_num at * <;> omega

theorem extract_high {n a b : Nat} {u v : Int}
    (hn : n=19 ∨ n=20) (ha : a<2^20) (hb : b<2^20)
    (h : |u|+|v|≤(2:Int)^n) (hu : -(2:Int)^(n-1)≤u) :
    let z := (u*((a:Int)-2^41)+v*((b:Int)-2^62))/2^n
    (BitVec.ofInt 64 (z+2^20+2^41)).sshiftRight (62-n) =
      BitVec.ofInt 64 (-v) := by
  dsimp only
  rw [signed_shift_ofInt (biased_row_signed hn ha hb h),
    packed20_extract_high hn ha hb h hu]

/-- A wrapped arithmetic shift still has the exact low 44 quotient bits. -/
theorem shifted_low44 (x : Int) :
    (((BitVec.ofInt 64 x).sshiftRight 20).toNat : Int)%2^44 =
      (x/2^20)%2^44 := by
  rw [BitVec.sshiftRight_eq,VG.Proof.Divstep.toNat_ofInt64,
    Int.shiftRight_eq_div_pow,BitVec.toInt_ofInt,Int.bmod_def]
  norm_num
  split <;> omega

end VG.Proof.P256.EcdhInverse
