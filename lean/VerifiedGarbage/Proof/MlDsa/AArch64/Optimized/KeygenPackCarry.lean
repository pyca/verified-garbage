import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackStream

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64

theorem digit_tail (G a d c : Nat) :
    (G/2^a%2^d)/2^c=G%2^(a+d)/2^(a+c) := by
  rw [Nat.pow_add 2 a c,←Nat.div_div_eq_div_mul,Nat.pow_add 2 a d,Nat.mod_mul_right_div_self]

theorem digit_lt64 (G d j : Nat) (hd : d≤20) : G/2^(d*j)%2^d<2^64 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem acc64_lt64 (G d j : Nat) : acc64 G d j<2^64 :=
  Nat.lt_of_lt_of_le (acc64_lt G d j)
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem fieldAcc_next (G d j : Nat) (hd : d≤20) (hn : d*(j+1)%64≠0) :
    fieldAcc d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (acc64 G d (j+1)) := by
  have ha : d*(j+1)=d*j+d := Nat.mul_succ _ _
  by_cases hc : 64<d*j%64+d
  · rw [fieldAcc,ite_eq_left hc]
    have hb : 64*(d*(j+1)/64)=d*j+(64-d*j%64) := by rw [ha]; omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (digit_lt64 G d j hd),BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (acc64_lt64 G d (j+1))]
    rw [digit_tail,acc64,hb,ha]
  · rw [fieldAcc,ite_eq_right hc,joined_acc]
    have hb : d*(j+1)/64=d*j/64 := by rw [ha] at hn ⊢; omega
    rw [acc64,hb]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
