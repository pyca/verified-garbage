import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackField

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlDsa.Pack

def acc64 (G d j : Nat) : Nat := G%2^(d*j)/2^(64*(d*j/64))

theorem acc64_lt (G d j : Nat) : acc64 G d j<2^(d*j%64) := by
  have h := mod_div_lt G (d*j) (64*(d*j/64))
  simpa only [acc64,show d*j-64*(d*j/64)=d*j%64 by omega] using h

theorem add64 (G d j : Nat) :
    acc64 G d j+(G/2^(d*j)%2^d)*2^(d*j%64)=
      G%2^(d*(j+1))/2^(64*(d*j/64)) := by
  unfold acc64
  rw [Nat.mul_succ,mod_two_pow_add,two_pow_split (show 64*(d*j/64)≤d*j by omega),
    show d*j-64*(d*j/64)=d*j%64 by omega,Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.mul_comm (2^(d*j%64))]

theorem ofNat_shift (v sh : Nat) :
    (BitVec.ofNat 64 v<<<sh)=BitVec.ofNat 64 (v*2^sh) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_mul_mod]

theorem joined_nat (d j a v : Nat) (ha : a<2^(d*j%64)) :
    joined d j (BitVec.ofNat 64 a) (BitVec.ofNat 64 v)=
      BitVec.ofNat 64 (a+v*2^(d*j%64)) := by
  unfold joined
  split
  · rename_i h
    have hz : a=0 := by simpa only [h,Nat.pow_zero,Nat.lt_one_iff] using ha
    simp only [hz,h,Nat.pow_zero,Nat.mul_one,Nat.zero_add]
  · rw [ofNat_shift,←BitVec.ofNat_or,Nat.or_comm,
      Nat.mul_comm v,←Nat.two_pow_add_eq_or_of_lt ha v,Nat.add_comm]

theorem joined_acc (G d j : Nat) :
    joined d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (G%2^(d*(j+1))/2^(64*(d*j/64))) := by
  rw [joined_nat _ _ _ _ (acc64_lt G d j),add64]

theorem joined_flush {G d j : Nat} (h : 64≤d*j%64+d) :
    joined d j (BitVec.ofNat 64 (acc64 G d j)) (BitVec.ofNat 64 (G/2^(d*j)%2^d))=
      BitVec.ofNat 64 (G/2^(64*(d*j/64))) := by
  rw [joined_acc]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact VG.Proof.MlKem.mod_pow_div_mod G (by rw [Nat.mul_succ]; omega)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
