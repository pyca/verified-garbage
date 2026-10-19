module

public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecMath
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecSpec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

/-! # The decoder reads exactly twelve bytes -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64

theorem input_byte (m : Mem) (a : Addr) {j : Nat} (hj : j<12) :
    vbyte (ofVDwords (m.readW a 64) ((m.readW (a+8) 32).setWidth 64)) j =
      m (a+BitVec.ofNat 64 j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte,ofVDwords,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : j<8
  · rw [ite_eq_left (by omega)]
    simp only [Mem.readW,BitVec.getLsbD_setWidth,show 8*j+i<64 by omega,decide_true,Bool.true_and]
    rw [getLsbD_read _ 8 _ _ (by omega)]
    simp only [show (8*j+i)/8=j by omega,show (8*j+i)%8=i by omega]
  · rw [ite_eq_right (by omega)]
    simp only [Mem.readW,BitVec.getLsbD_setWidth,show 8*j+i-64<64 by omega,
      show 8*j+i-64<32 by omega,decide_true,Bool.true_and]
    rw [getLsbD_read _ 4 _ _ (by omega)]
    simp only [show (8*j+i-64)/8=j-8 by omega,show (8*j+i-64)%8=i by omega]
    rw [show (8:BitVec 64)=BitVec.ofNat 64 8 from rfl,ptr_add,show 8+(j-8)=j by omega]


theorem decoded_spec (s : State) {k : Nat} (hk : k<32) {x : BitVec 128}
    (hx : ∀ j<12, (vbyte x j).toNat = Decode12.byte s (12*k+j)) {e : Nat} (he : e<4) :
    vword (decoded x .zip1) e = Decode12.G s (8*k+e) ∧
    vword (decoded x .zip2) e = Decode12.G s (8*k+4+e) := by
  have hl := dec_low_spec s hk hx
  have hh := dec_high_spec s hk hx
  rw [decoded,decoded,vword_zip1_s4' _ _ he,vword_zip2_s4 _ _ he]
  by_cases h : e%2=0
  · rw [ite_eq_left h,ite_eq_left h]
    constructor <;> apply BitVec.eq_of_toNat_eq
    · rw [hl _ (by omega)]
      dsimp only
      rw [show 8*k+2*(e/2)=8*k+e by omega]
    · rw [hl _ (by omega)]
      dsimp only
      rw [show 8*k+2*(2+e/2)=8*k+4+e by omega]
  · rw [ite_eq_right h,ite_eq_right h]
    constructor <;> apply BitVec.eq_of_toNat_eq
    · rw [hh _ (by omega)]
      dsimp only
      rw [show 8*k+(2*(e/2)+1)=8*k+e by omega]
    · rw [hh _ (by omega)]
      dsimp only
      rw [show 8*k+(2*(2+e/2)+1)=8*k+4+e by omega]

end VG.Proof.MlKem.AArch64.Codec16
