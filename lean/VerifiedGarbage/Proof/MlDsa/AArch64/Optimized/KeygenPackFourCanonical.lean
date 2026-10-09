import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackStreamMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits)

theorem nibble_pair (a b : Nat) (ha : a<16) (hb : b<16) :
    (BitVec.ofNat 4 a).setWidth 8 ||| ((BitVec.ofNat 4 b).setWidth 8<<<4)=
      BitVec.ofNat 8 (a+16*b) := by
  have hA : (BitVec.ofNat 4 a).setWidth 8=BitVec.ofNat 8 a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,show 2^4=16 by decide,Nat.mod_eq_of_lt ha]
  have hB : (BitVec.ofNat 4 b).setWidth 8=BitVec.ofNat 8 b := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,show 2^4=16 by decide,Nat.mod_eq_of_lt hb]
  rw [hA,hB]
  have hshift : (BitVec.ofNat 8 b<<<4)=BitVec.ofNat 8 (16*b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_mul_mod]
    rw [Nat.mul_comm b]
  rw [hshift,←BitVec.ofNat_or,Nat.or_comm,←Nat.two_pow_add_eq_or_of_lt (show a<2^4 from ha) b,Nat.add_comm]

theorem four_byte (V : Nat → Nat) (hV : ∀j<16,V j<16) {i : Nat} (hi : i<8) :
    byteOf (digits 4 ((List.range 16).map V)) i=
      (BitVec.ofNat 4 (V (2*i))).setWidth 8 ||| ((BitVec.ofNat 4 (V (2*i+1))).setWidth 8<<<4) := by
  rw [nibble_pair _ _ (hV _ (by omega)) (hV _ (by omega))]
  let G := digits 4 ((List.range 16).map V)
  have h0 := digits_range_get (d:=4) (c:=16) hV (show 2*i<16 by omega)
  have h1 := digits_range_get (d:=4) (c:=16) hV (show 2*i+1<16 by omega)
  change G/2^(4*(2*i))%16=V (2*i) at h0
  change G/2^(4*(2*i+1))%16=V (2*i+1) at h1
  apply BitVec.eq_of_toNat_eq
  change (G/2^(8*i))%256=(V (2*i)+16*V (2*i+1))%256
  have hsum : V (2*i)+16*V (2*i+1)<256 := by have := hV (2*i) (by omega);have := hV (2*i+1) (by omega);omega
  rw [Nat.mod_eq_of_lt hsum,show 256=16*16 by decide,Nat.mod_mul]
  rw [show 8*i=4*(2*i) by omega,h0]
  congr 1
  rw [show 16=2^4 by decide,Nat.div_div_eq_div_mul,←Nat.pow_add,
    show 4*(2*i)+4=4*(2*i+1) by omega]
  exact congrArg (16*·) h1

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
