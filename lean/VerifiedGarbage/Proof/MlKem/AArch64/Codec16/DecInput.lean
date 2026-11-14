module

public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
import VerifiedGarbage.Proof.MlKem.Encode

/-! ### `MlKem.AArch64.Codec16.DecMath`, which only this module used -/

section

/-! # SIMD decoder arithmetic -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Codec16 (decMath)

def decoded (x : BitVec 128) (part : VPermOp) : BitVec 128 :=
  VPermOp.eval part .s4 (reduced (low x)) (reduced (high x))

theorem dec_math_ok (s : State) (h16 : s.v .v16 = decMask) (h17 : s.v .v17 = mask12)
    (h18 : s.v .v18 = qvec) : WP isa (.block decMath) s fun t =>
    t.v .v0 = decoded (ofVDwords (s.gpr .x9) (s.gpr .x10)) .zip1 ∧
    t.v .v1 = decoded (ofVDwords (s.gpr .x9) (s.gpr .x10)) .zip2 ∧
    t.gpr=s.gpr ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
    (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → t.v r = s.v r) := by
  unfold decMath
  rrun [h16,h17,h18,VG.AArch64.setLane_pair_hi,VShiftOp.eval,decoded,low,high,reduced,tbl,
    RegUpd.sp_setV]
  refine ⟨by rfl,by rfl,?_⟩
  intro r h0 h1 h2 h3 h4
  simp only [h0,h1,h2,h3,h4,ite_false]

end VG.Proof.MlKem.AArch64.Codec16

end

end

/-! ### `MlKem.AArch64.Codec16.DecSpec`, which only this module used -/

section

/-! # Decoded lanes implement ByteDecode12 for arbitrary input bytes -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem


theorem even_nat (s : State) {g : Nat} (hg : g<128) :
    (Decode12.G s (2*g)).toNat =
      (Decode12.byte s (3*g)+Decode12.byte s (3*g+1)%16*256)%3329 := by
  have hq : q=3329 := rfl
  have h0 : Decode12.byte s (3*g)<256 := byte_lt _
  rw [Decode12.G_even s hg,BitVec.toNat_ofNat,condSub_eq (by omega_using [hq, h0])]
  have := Nat.mod_lt (Decode12.byte s (3*g)+Decode12.byte s (3*g+1)%16*256) (show 0<q by decide)
  rw [hq] at *
  omega_using []

theorem odd_nat (s : State) {g : Nat} (hg : g<128) :
    (Decode12.G s (2*g+1)).toNat =
      (Decode12.byte s (3*g+1)/16+Decode12.byte s (3*g+2)*16)%3329 := by
  have hq : q=3329 := rfl
  have h1 : Decode12.byte s (3*g+1)<256 := byte_lt _
  have h2 : Decode12.byte s (3*g+2)<256 := byte_lt _
  rw [Decode12.G_odd s hg,BitVec.toNat_ofNat,condSub_eq (by omega_using [hq, h1, h2])]
  have := Nat.mod_lt (Decode12.byte s (3*g+1)/16+Decode12.byte s (3*g+2)*16) (show 0<q by decide)
  rw [hq] at *
  omega_using []

theorem dec_low_spec (s : State) {k : Nat} (hk : k<32) {x : BitVec 128}
    (hx : ∀ j<12, (vbyte x j).toNat = Decode12.byte s (12*k+j)) :
    Lanes (reduced (low x)) (fun e => (Decode12.G s (8*k+2*e)).toNat) := by
  refine (reduced_lanes (low_lanes x) (fun e _ => by omega_using [])).congr ?_
  intro e he
  rw [hx _ (by omega_using [he]),hx _ (by omega_using [he]),hx _ (by omega_using [he]),
    show 8*k+2*e=2*(4*k+e) by omega_using [],even_nat s (by omega_using [hk, he])]
  rw [show 3*(4*k+e)=12*k+3*e by omega_using []]
  simp only [Nat.add_assoc]
  have h0 : Decode12.byte s (12*k+3*e)<256 := byte_lt _
  have h1 : Decode12.byte s (12*k+(3*e+1))<256 := byte_lt _
  congr 1
  omega_using [h0]

theorem dec_high_spec (s : State) {k : Nat} (hk : k<32) {x : BitVec 128}
    (hx : ∀ j<12, (vbyte x j).toNat = Decode12.byte s (12*k+j)) :
    Lanes (reduced (high x)) (fun e => (Decode12.G s (8*k+(2*e+1))).toNat) := by
  have hf : ∀ e<4,
      ((vbyte x (3*e)).toNat+256*(vbyte x (3*e+1)).toNat+65536*(vbyte x (3*e+2)).toNat)/4096 < 6658 := by
    intro e _
    have := (vbyte x (3*e)).isLt
    have := (vbyte x (3*e+1)).isLt
    have := (vbyte x (3*e+2)).isLt
    omega_using []
  refine (reduced_lanes (high_lanes x) hf).congr ?_
  intro e he
  rw [hx _ (by omega_using [he]),hx _ (by omega_using [he]),hx _ (by omega_using [he]),
    show 8*k+(2*e+1)=2*(4*k+e)+1 by omega_using [],odd_nat s (by omega_using [hk, he])]
  rw [show 3*(4*k+e)=12*k+3*e by omega_using []]
  simp only [Nat.add_assoc]
  have h0 : Decode12.byte s (12*k+3*e)<256 := byte_lt _
  have h1 : Decode12.byte s (12*k+(3*e+1))<256 := byte_lt _
  congr 1
  omega_using [h0]

end VG.Proof.MlKem.AArch64.Codec16

end

end


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
  · rw [ite_eq_left (by omega_using [hi, h])]
    simp only [Mem.readW,BitVec.getLsbD_setWidth,show 8*j+i<64 by omega_using [hi, h],decide_true,Bool.true_and]
    rw [getLsbD_read _ 8 _ _ (by omega_using [hi, h])]
    simp only [show (8*j+i)/8=j by omega_using [hi],show (8*j+i)%8=i by omega_using [hi]]
  · rw [ite_eq_right (by omega_using [h])]
    simp only [Mem.readW,BitVec.getLsbD_setWidth,show 8*j+i-64<64 by omega_using [hj, hi],
      show 8*j+i-64<32 by omega_using [hj, hi],decide_true,Bool.true_and]
    rw [getLsbD_read _ 4 _ _ (by omega_using [hj, hi])]
    simp only [show (8*j+i-64)/8=j-8 by omega_using [hi],show (8*j+i-64)%8=i by omega_using [hi, h]]
    rw [show (8:BitVec 64)=BitVec.ofNat 64 8 from rfl,ptr_add,show 8+(j-8)=j by omega_using [h]]


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
    · rw [hl _ (by omega_using [he])]
      dsimp only
      rw [show 8*k+2*(e/2)=8*k+e by omega_using [h]]
    · rw [hl _ (by omega_using [he])]
      dsimp only
      rw [show 8*k+2*(2+e/2)=8*k+4+e by omega_using [h]]
  · rw [ite_eq_right h,ite_eq_right h]
    constructor <;> apply BitVec.eq_of_toNat_eq
    · rw [hh _ (by omega_using [he])]
      dsimp only
      rw [show 8*k+(2*(e/2)+1)=8*k+e by omega_using [h]]
    · rw [hh _ (by omega_using [he])]
      dsimp only
      rw [show 8*k+(2*(2+e/2)+1)=8*k+4+e by omega_using [h]]

end VG.Proof.MlKem.AArch64.Codec16
