import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Divstep.BatchBasic

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64

/-- The existing LSR/SUB/EXTR sequence implements an arithmetic right shift. -/
theorem signed_extract (x : BitVec 64) {k : Nat} (hk : k<64) :
    ((-(x >>> 63)) ++ x).extractLsb' k 64 = x.sshiftRight k := by
  rw [msb_word]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_append,
    BitVec.getLsbD_sshiftRight,show ¬64≤i by omega,decide_false,
    Bool.not_false,Bool.true_and]
  by_cases hki : k+i<64
  · simp only [hki,↓reduceIte,hi,decide_true,Bool.true_and]
  · simp only [hki,↓reduceIte]
    cases x.msb
    · simp only [Bool.false_eq_true,↓reduceIte,hi,decide_true,Bool.true_and]
      change (0 : BitVec 64).getLsbD (k+i-64)=false
      exact BitVec.getLsbD_zero
    · simp only [↓reduceIte,hi,decide_true,Bool.true_and,
        show -(1 : BitVec 64)=BitVec.allOnes 64 by decide,
        BitVec.getLsbD_allOnes,show k+i-64<64 by omega,decide_true]


/-- Signed shifts agree with integer division on a representable input. -/
theorem signed_shift_ofInt {x : Int} {k : Nat}
    (hx : -(2^63)≤x ∧ x<2^63) :
    (BitVec.ofInt 64 x).sshiftRight k = BitVec.ofInt 64 (x / 2^k) := by
  rw [BitVec.sshiftRight_eq,BitVec.toInt_ofInt_eq_self (by decide) hx.1 hx.2,
    Int.shiftRight_eq_div_pow]
  norm_cast


/-- Testing bit one before halving is testing parity afterwards. -/
theorem half_parity (x : BitVec 64) :
    (x.sshiftRight 1 &&& 1 = 0) ↔ (x &&& 2 = 0) := by
  rw [show (1 : BitVec 64)=BitVec.twoPow 64 0 by decide,
    show (2 : BitVec 64)=BitVec.twoPow 64 1 by decide,
    BitVec.and_twoPow,BitVec.and_twoPow]
  simp only [BitVec.getLsbD_sshiftRight,show ¬64≤0 by decide,decide_false,
    Bool.not_false,Bool.true_and,show (1:Nat)+0<64 by decide,↓reduceIte,Nat.add_zero]
  cases x.getLsbD 1 <;> decide


theorem msb_ofInt {d : Int} (hd : -(2^63)≤d ∧ d<2^63) :
    (BitVec.ofInt 64 d).msb = decide (d<0) := by
  have hi := BitVec.toInt_ofInt_eq_self (w:=64) (by decide) hd.1 hd.2
  cases h : (BitVec.ofInt 64 d).msb
  · have hn := BitVec.toInt_nonneg_of_msb_false h
    rw [hi] at hn
    exact (decide_eq_false (by omega)).symm
  · have hn := BitVec.toInt_neg_of_msb_true h
    rw [hi] at hn
    exact (decide_eq_true hn).symm


theorem ofInt_parity (g : Int) : (BitVec.ofInt 64 g &&& 1 = 0) ↔ g%2=0 := by
  have hc : ((BitVec.ofInt 64 g).toNat : Int)%2=g%2 := by
    rw [VG.Proof.Divstep.toNat_ofInt64,Int.emod_emod_of_dvd _ (by decide)]
  rw [VG.Proof.Divstep.and_one_word]
  by_cases h : (BitVec.ofInt 64 g).toNat%2=1
  · rw [ite_eq_left h]
    have hh : g%2=1 := by omega
    simp only [hh]
    decide
  · rw [ite_eq_right h]
    have hh : g%2=0 := by omega
    simp only [hh]

end VG.Proof.P256.EcdhInverse
