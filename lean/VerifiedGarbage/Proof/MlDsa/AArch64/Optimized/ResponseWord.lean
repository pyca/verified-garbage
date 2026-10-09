import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa

def reduceWord (x : BitVec 32) : BitVec 32 :=
  x-(x+4194304#32).sshiftRight 23*8380417#32

theorem reduceWord_eq (x : BitVec 32) (hl : -2*8380417<x.toInt) (hh : x.toInt<3*8380417) :
    reduceWord x=BitVec.ofInt 32 (reduce32 x.toInt) := by
  have hadd : (x+4194304#32).toInt=x.toInt+4194304 := by
    exact addWord_int _ _ (by change -2147483648≤x.toInt+4194304; omega)
      (by change x.toInt+4194304<2147483648; omega)
  have hshift : BitVec.ofInt 32 ((x.toInt+4194304)/8388608)=(x+4194304#32).sshiftRight 23 := by
    have h := BitVec.toInt_sshiftRight (x := x+4194304#32) (n := 23)
    rw [Int.shiftRight_eq_div_pow,hadd] at h
    change ((x+4194304#32).sshiftRight 23).toInt=(x.toInt+4194304)/8388608 at h
    rw [← h,BitVec.ofInt_toInt]
  unfold reduceWord reduce32
  rw [Int.sub_eq_add_neg,BitVec.ofInt_add,BitVec.ofInt_neg,BitVec.ofInt_mul,BitVec.ofInt_toInt,hshift]
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem reduceWord_int (x : BitVec 32) (hl : -2*8380417<x.toInt) (hh : x.toInt<3*8380417) :
    (reduceWord x).toInt=reduce32 x.toInt := by
  rw [reduceWord_eq x hl hh]
  have h := reduce32_bounds hl hh
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

/-- Four-instruction norm check: the accepted interval is exactly (-B,B).
The generous signed bound includes every reduced z, r0 and ct0 lane. -/
theorem norm_interval (x : BitVec 32) (B : Nat)
    (hB : 1≤B) (hB' : B≤524288)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) :
    (x+BitVec.ofNat 32 (B-1)).toNat<2*B-1 ↔ -(B:Int)<x.toInt ∧ x.toInt<(B:Int) := by
  have hx := BitVec.toInt_eq_toNat_cond x
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  split at hx <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
