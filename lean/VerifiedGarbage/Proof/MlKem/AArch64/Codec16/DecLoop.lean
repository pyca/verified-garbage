module

public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-! ### `MlKem.AArch64.Codec16.DecInput`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Codec16.DecLanes`, which this module and modules that import it used -/

section

/-! # Three input bytes expanded into a word -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def decMask : BitVec 128 := ofVBytes fun j =>
  if j%4 < 3 then BitVec.ofNat 8 (3*(j/4)+j%4) else 255

theorem dec_byte (x : BitVec 128) {e j : Nat} (he : e<4) (hj : j<4) :
    vbyte (tbl x decMask) (4*e+j) = if j<3 then vbyte x (3*e+j) else 0 := by
  rw [tbl,vbyte_ofVBytes _ (by omega_using [he, hj]),decMask,vbyte_ofVBytes _ (by omega_using [he, hj])]
  simp only [show (4*e+j)%4=j by omega_using [hj],show (4*e+j)/4=e by omega_using [hj]]
  by_cases h : j<3
  · simp only [h,ite_true,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 3*e+j<256 by omega_using [he, hj]),
      show 3*e+j<16 by omega_using [he, hj],ite_true]
  · simp only [h,ite_false]
    rfl

theorem word_bytes (x : BitVec 128) (e : Nat) :
    vword x e = vbyte x (4*e+3) ++ (vbyte x (4*e+2) ++ (vbyte x (4*e+1) ++ vbyte x (4*e))) := by
  rw [VG.Proof.MlKem.AArch64.Ntt16.vword_halves,Cbd16.half_bytes,Cbd16.half_bytes]
  rw [show 2*(2*e+1)+1=4*e+3 by omega_using [],show 2*(2*e+1)=4*e+2 by omega_using [],
    show 2*(2*e)+1=4*e+1 by omega_using [],show 2*(2*e)=4*e by omega_using [],BitVec.append_assoc]
  rfl

theorem dec_words (x : BitVec 128) {e : Nat} (he : e<4) :
    (vword (tbl x decMask) e).toNat =
      (vbyte x (3*e)).toNat + 256*(vbyte x (3*e+1)).toNat + 65536*(vbyte x (3*e+2)).toNat := by
  rw [word_bytes]
  rw [dec_byte x he (by decide : 3<4),dec_byte x he (by decide : 2<4),
    dec_byte x he (by decide : 1<4),show 4*e=4*e+0 by omega_using [],dec_byte x he (by decide : 0<4)]
  simp only [show ¬ (3<3) by decide,show 2<3 by decide,show 1<3 by decide,show 0<3 by decide,
    ite_false,ite_true,Nat.add_zero,BitVec.toNat_append]
  change (0 <<< 24 ||| ((vbyte x (3*e+2)).toNat <<< 16 |||
    ((vbyte x (3*e+1)).toNat <<< 8 ||| (vbyte x (3*e)).toNat))) = _
  rw [Nat.zero_shiftLeft,Nat.zero_or,← Nat.shiftLeft_add_eq_or_of_lt
    (i:=8) (vbyte x (3*e) |>.isLt)]
  have small : ((vbyte x (3*e+1)).toNat <<< 8)+(vbyte x (3*e)).toNat < 2^16 := by
    rw [Nat.shiftLeft_eq]
    have := (vbyte x (3*e)).isLt
    have := (vbyte x (3*e+1)).isLt
    omega_using []
  rw [← Nat.shiftLeft_add_eq_or_of_lt small]
  simp only [Nat.shiftLeft_eq]
  omega_using []

def qvec : BitVec 128 := ofVWords 3329 3329 3329 3329
def mask12 : BitVec 128 := ofVWords 4095 4095 4095 4095

def low (x : BitVec 128) : BitVec 128 := tbl x decMask &&& mask12
def high (x : BitVec 128) : BitVec 128 := VArr.s4.map2 (fun _ _ y => y >>> 12) 0 (tbl x decMask)
def reduced (x : BitVec 128) : BitVec 128 :=
  VArr.s4.map2 (fun _ a b => if a.toNat ≤ b.toNat then a else b) x
    (VArr.s4.map2 (fun _ a b => a-b) x qvec)

theorem vword_and (x y : BitVec 128) (e : Nat) : vword (x &&& y) e = vword x e &&& vword y e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [vword,hi]

theorem low_lanes (x : BitVec 128) : Lanes (low x) fun e =>
    ((vbyte x (3*e)).toNat+256*(vbyte x (3*e+1)).toNat+65536*(vbyte x (3*e+2)).toNat)%4096 := by
  intro e he
  rw [low,vword_and,mask12,vword_dup_s4 _ he,BitVec.toNat_and,dec_words _ he]
  exact Nat.and_two_pow_sub_one_eq_mod _ 12

theorem high_lanes (x : BitVec 128) : Lanes (high x) fun e =>
    ((vbyte x (3*e)).toNat+256*(vbyte x (3*e+1)).toNat+65536*(vbyte x (3*e+2)).toNat)/4096 := by
  intro e he
  rw [high,vword_map2 _ _ _ he,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,dec_words _ he]

theorem reduced_lanes {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f)
    (hf : ∀ e<4, f e<6658) : Lanes (reduced x) fun e => f e%3329 := by
  have hq : Lanes qvec fun _ => 3329 := by
    intro e he; rw [qvec,vword_dup_s4 _ he]; rfl
  apply (lanes_umin hx (lanes_sub hx hq)).congr
  intro e he
  have := hf e he
  omega_using [this]

end VG.Proof.MlKem.AArch64.Codec16

end

end

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

end

end

/-! # Eight-coefficient decoding loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Codec16 (decMath maskVec)
open VG.Proof.Rc4.AArch64


theorem decMask_value : decMask = 0xff0b0a09ff080706ff050403ff020100#128 := by
  apply vbyte_ext
  exact (by decide +kernel : ∀ e<16, vbyte decMask e = vbyte 0xff0b0a09ff080706ff050403ff020100#128 e)

end VG.Proof.MlKem.AArch64.Codec16
