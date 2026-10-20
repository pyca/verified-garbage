module

public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Three input bytes expanded into a word -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def decMask : BitVec 128 := ofVBytes fun j =>
  if j%4 < 3 then BitVec.ofNat 8 (3*(j/4)+j%4) else 255

theorem dec_byte (x : BitVec 128) {e j : Nat} (he : e<4) (hj : j<4) :
    vbyte (tbl x decMask) (4*e+j) = if j<3 then vbyte x (3*e+j) else 0 := by
  rw [tbl,vbyte_ofVBytes _ (by omega),decMask,vbyte_ofVBytes _ (by omega)]
  simp only [show (4*e+j)%4=j by omega,show (4*e+j)/4=e by omega]
  by_cases h : j<3
  · simp only [h,ite_true,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 3*e+j<256 by omega),
      show 3*e+j<16 by omega,ite_true]
  · simp only [h,ite_false]
    rfl

theorem word_bytes (x : BitVec 128) (e : Nat) :
    vword x e = vbyte x (4*e+3) ++ (vbyte x (4*e+2) ++ (vbyte x (4*e+1) ++ vbyte x (4*e))) := by
  rw [VG.Proof.MlKem.AArch64.Ntt16.vword_halves,Cbd16.half_bytes,Cbd16.half_bytes]
  rw [show 2*(2*e+1)+1=4*e+3 by omega,show 2*(2*e+1)=4*e+2 by omega,
    show 2*(2*e)+1=4*e+1 by omega,show 2*(2*e)=4*e by omega,BitVec.append_assoc]
  rfl

theorem dec_words (x : BitVec 128) {e : Nat} (he : e<4) :
    (vword (tbl x decMask) e).toNat =
      (vbyte x (3*e)).toNat + 256*(vbyte x (3*e+1)).toNat + 65536*(vbyte x (3*e+2)).toNat := by
  rw [word_bytes]
  rw [dec_byte x he (by decide : 3<4),dec_byte x he (by decide : 2<4),
    dec_byte x he (by decide : 1<4),show 4*e=4*e+0 by omega,dec_byte x he (by decide : 0<4)]
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
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt small]
  simp only [Nat.shiftLeft_eq]
  omega

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
  omega

end VG.Proof.MlKem.AArch64.Codec16
