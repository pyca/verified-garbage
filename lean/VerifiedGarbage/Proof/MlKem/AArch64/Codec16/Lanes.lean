module
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Spec.MlKem

import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Vector coefficient packing and byte selection -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def packed (x y : BitVec 128) : BitVec 128 :=
  VPermOp.eval .uzp1 .s4 x y |||
    VArr.s4.map2 (fun _ _ b => b <<< 12) 0 (VPermOp.eval .uzp2 .s4 x y)

theorem vword_or (x y : BitVec 128) (e : Nat) :
    vword (x ||| y) e = vword x e ||| vword y e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [vword,hi]

theorem pair_toNat (a b : BitVec 32) (ha : a.toNat < 4096) (hb : b.toNat < 4096) :
    (a ||| b <<< 12).toNat = a.toNat + 4096*b.toNat := by
  rw [BitVec.toNat_or,BitVec.toNat_shiftLeft,Nat.mod_eq_of_lt (by omega)]
  rw [Nat.or_comm,← Nat.shiftLeft_add_eq_or_of_lt (i:=12) ha, Nat.shiftLeft_eq]
  omega

theorem packed_lanes {x y : BitVec 128} {f : Nat → Nat}
    (hx : Lanes x f) (hy : Lanes y (fun e => f (4+e)))
    (hf : ∀ e < 8, f e < 4096) :
    Lanes (packed x y) (fun e => f (2*e) + 4096*f (2*e+1)) := by
  intro e he
  rw [packed,vword_or,vword_map2 _ _ _ he,vword_uzp1_s4 _ _ he,vword_uzp2_s4 _ _ he]
  by_cases h : e < 2
  · rw [ite_eq_left h,ite_eq_left h,pair_toNat _ _
      (by rw [hx _ (by omega)]; exact hf _ (by omega))
      (by rw [hx _ (by omega)]; exact hf _ (by omega)),hx _ (by omega),hx _ (by omega)]
  · rw [ite_eq_right h,ite_eq_right h,pair_toNat _ _
      (by rw [hy _ (by omega)]; exact hf _ (by omega))
      (by rw [hy _ (by omega)]; exact hf _ (by omega)),hy _ (by omega),hy _ (by omega)]
    simp only [show 4+2*(e-2)=2*e by omega,show 4+(2*(e-2)+1)=2*e+1 by omega]

theorem vbyte_word (x : BitVec 128) (j : Nat) :
    vbyte x j = (vword x (j/4)).extractLsb' (8*(j%4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte,vword,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,
    show 8*(j%4)+i < 32 by omega]
  exact congrArg _ (by omega)

def encMask : BitVec 128 := ofVBytes fun j =>
  if j < 12 then BitVec.ofNat 8 (4*(j/3)+j%3) else 255

def tbl (x mask : BitVec 128) : BitVec 128 := ofVBytes fun i =>
  let j := (vbyte mask i).toNat
  if j < 16 then vbyte x j else 0

theorem enc_byte (x : BitVec 128) {j : Nat} (hj : j < 12) :
    vbyte (tbl x encMask) j = (vword x (j/3)).extractLsb' (8*(j%3)) 8 := by
  rw [tbl,vbyte_ofVBytes _ (by omega),encMask,vbyte_ofVBytes _ (by omega)]
  simp only [hj,ite_true,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4*(j/3)+j%3 < 256 by omega),
    show 4*(j/3)+j%3 < 16 by omega,ite_true]
  rw [vbyte_word]
  simp only [show (4*(j/3)+j%3)/4=j/3 by omega,show (4*(j/3)+j%3)%4=j%3 by omega]


theorem enc_spec (P : VG.Spec.MlKem.Poly) {k : Nat} (hk : k < 32) {x y : BitVec 128}
    (hx : Lanes x (fun e => (P[8*k+e]!).val))
    (hy : Lanes y (fun e => (P[8*k+(4+e)]!).val)) {j : Nat} (hj : j < 12) :
    vbyte (tbl (packed x y) encMask) j = (VG.Spec.MlKem.encode12 P)[12*k+j]! := by
  have hp := packed_lanes hx hy (fun e _ => VG.Proof.MlKem.val_lt_4096 (P[8*k+e]!))
  rw [show 12*k+j = 3*(4*k+j/3)+j%3 by omega,
    VG.Proof.MlKem.encode12_group P (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [enc_byte _ hj,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    hp _ (by omega),BitVec.toNat_ofNat]
  simp only [show 8*k+2*(j/3) = 2*(4*k+j/3) by omega,
    show 8*k+(2*(j/3)+1) = 2*(4*k+j/3)+1 by omega]

end VG.Proof.MlKem.AArch64.Codec16
