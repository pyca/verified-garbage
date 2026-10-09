import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackTailWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackSpec

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Proof.MlKem (digits digits_cons digits_nil)

private theorem or_shift_add {a : Nat} (k b : Nat) (ha : a<2^k) :
    a ||| (b <<< k)=a+b*2^k := by
  rw [Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt ha,Nat.shiftLeft_eq,Nat.add_comm]

/-- Bounded four-bit fields occupy disjoint nibbles, so OR is exact addition. -/
theorem nibble_value (a b : BitVec 8) (ha : a.toNat<16) (hb : b.toNat<16) :
    (a ||| (b <<< 4)).toNat=a.toNat+16*b.toNat := by
  rw [BitVec.toNat_or,BitVec.toNat_shiftLeft]
  have hmod : (b.toNat <<< 4)%2^8=b.toNat <<< 4 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    omega
  rw [hmod,or_shift_add 4 b.toNat ha]
  omega

/-- Four six-bit coefficients form exactly one 24-bit base-64 integer. -/
theorem sixWord_value (a b c d : BitVec 8)
    (ha : a.toNat<64) (hb : b.toNat<64) (hc : c.toNat<64) (hd : d.toNat<64) :
    (sixWord a b c d).toNat=a.toNat+64*b.toNat+4096*c.toNat+262144*d.toNat := by
  simp only [sixWord,BitVec.toNat_or,BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth_of_le (by decide : 8≤32)]
  have m6 : (b.toNat <<< 6)%2^32=b.toNat <<< 6 := by
    apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq]; omega
  have m12 : (c.toNat <<< 12)%2^32=c.toNat <<< 12 := by
    apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq]; omega
  have m18 : (d.toNat <<< 18)%2^32=d.toNat <<< 18 := by
    apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq]; omega
  rw [m6,m12,m18,or_shift_add 6 b.toNat ha,
    or_shift_add 12 c.toNat (by omega),or_shift_add 18 d.toNat (by omega)]
  omega

theorem nibble_digits (a b : BitVec 8) (ha : a.toNat<16) (hb : b.toNat<16) :
    a ||| (b <<< 4)=BitVec.ofNat 8 (digits 4 [a.toNat,b.toNat]) := by
  apply BitVec.eq_of_toNat_eq
  rw [nibble_value a b ha hb]
  simp only [digits_cons,digits_nil,Nat.mul_zero,Nat.add_zero,BitVec.toNat_ofNat]
  omega

theorem sixWord_digits (a b c d : BitVec 8)
    (ha : a.toNat<64) (hb : b.toNat<64) (hc : c.toNat<64) (hd : d.toNat<64) :
    (sixWord a b c d).toNat=digits 6 [a.toNat,b.toNat,c.toNat,d.toNat] := by
  rw [sixWord_value a b c d ha hb hc hd]
  simp only [digits_cons,digits_nil,Nat.mul_zero,Nat.add_zero]
  omega


/-- Extracting a stored byte agrees with the byte of the specification's
four-coefficient integer. -/
theorem sixWord_byte_digits (a b c d : BitVec 8)
    (ha : a.toNat<64) (hb : b.toNat<64) (hc : c.toNat<64) (hd : d.toNat<64) (i : Nat) :
    (sixWord a b c d).extractLsb' (8*i) 8 =
      BitVec.ofNat 8 (digits 6 [a.toNat,b.toNat,c.toNat,d.toNat]/2^(8*i)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb',
    Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
  rw [sixWord_digits a b c d ha hb hc hd]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
