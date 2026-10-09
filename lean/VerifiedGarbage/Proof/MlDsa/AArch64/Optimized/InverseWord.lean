import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseArithmetic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackWord

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse

/-- Exact lane expression of SSHR/AND/ADD/SUB/UMIN. -/
def canonicalWord (x : BitVec 32) : BitVec 32 :=
  let a := x + (x.sshiftRight 31 &&& 8380417#32)
  BitVec.ofNat 32 (min a.toNat (a-8380417#32).toNat)

def signCorrected (x : BitVec 32) : BitVec 32 :=
  x + (x.sshiftRight 31 &&& 8380417#32)

theorem signCorrected_int (x : BitVec 32) (hl : -8380417<x.toInt)
    (hh : x.toInt<2*8380417) :
    (signCorrected x).toInt = if x.toInt<0 then x.toInt+8380417 else x.toInt := by
  have ht := BitVec.toInt_eq_toNat_cond x
  simp only [signCorrected,ResidentMask.signMask32]
  by_cases hs : x.toNat<2^31
  · rw [ite_eq_left hs]
    simp only [show (0 : BitVec 32) &&& 8380417#32 = 0#32 by decide ]
    have hp : ¬x.toInt<0 := by omega
    rw [ite_eq_right hp]
    have h0 := addWord_int x (0#32) (by change -2147483648≤x.toInt+0; omega)
      (by change x.toInt+0<2147483648; omega)
    simpa only [show (0#32).toInt=0 by decide,Int.add_zero] using h0
  · rw [ite_eq_right hs]
    simp only [show (-1 : BitVec 32) &&& 8380417#32 = 8380417#32 by decide]
    have hp : x.toInt<0 := by omega
    rw [ite_eq_left hp]
    exact addWord_int _ _ (by change -2147483648≤x.toInt+8380417; omega)
      (by change x.toInt+8380417<2147483648; omega)

theorem min_sub_nat (a : BitVec 32) (ha : a.toNat<2*8380417) :
    (BitVec.ofNat 32 (min a.toNat (a-8380417#32).toNat)).toNat = a.toNat%8380417 := by
  rw [Nat.min_def]
  split <;> bv_omega

theorem canonicalWord_nat (x : BitVec 32) (hl : -8380417<x.toInt)
    (hh : x.toInt<2*8380417) : (canonicalWord x).toNat = (canonical x.toInt).toNat := by
  have he := signCorrected_int x hl hh
  have ht := BitVec.toInt_eq_toNat_cond (signCorrected x)
  have hi := (signCorrected x).isLt
  have hb : 0≤(signCorrected x).toInt ∧ (signCorrected x).toInt<2*8380417 := by
    rw [he]
    split <;> omega
  have hn : ((signCorrected x).toNat : Int) = (signCorrected x).toInt := by omega
  have hnat : (signCorrected x).toNat<2*8380417 := by omega
  change (BitVec.ofNat 32 (min (signCorrected x).toNat (signCorrected x-8380417#32).toNat)).toNat = _
  rw [min_sub_nat _ hnat]
  have hc := canonical_bounds hl hh
  have hm := canonical_mod x.toInt
  split at he <;> omega

theorem canonicalWord_bounds (x : BitVec 32) (hl : -8380417<x.toInt)
    (hh : x.toInt<2*8380417) : (canonicalWord x).toNat<8380417 := by
  rw [canonicalWord_nat x hl hh]
  have h := canonical_bounds hl hh
  omega

theorem canonicalWord_int (x : BitVec 32) (hl : -8380417<x.toInt)
    (hh : x.toInt<2*8380417) : (canonicalWord x).toInt=canonical x.toInt := by
  have hn := canonicalWord_nat x hl hh
  have hb := canonical_bounds hl hh
  have ht := BitVec.toInt_eq_toNat_cond (canonicalWord x)
  omega

theorem canonicalWord_field (x : BitVec 32) (hl : -8380417<x.toInt)
    (hh : x.toInt<2*8380417) : VG.Spec.MlDsa.ofInt (canonicalWord x).toInt=VG.Spec.MlDsa.ofInt x.toInt := by
  rw [canonicalWord_int x hl hh,canonical_field]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
