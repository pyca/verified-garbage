module
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec

/-! # Exact SIMD horizontal sum used for the rejection mask -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

def rotateHalves (x : BitVec 128) (k : Nat) : BitVec 128 :=
  ((x ++ x) >>> (16*k)).extractLsb' 0 128

theorem rotate_half (x : BitVec 128) {k e : Nat} (hk : k < 8) (he : e < 8) :
    vhalf (rotateHalves x k) e = vhalf x ((e+k)%8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vhalf, rotateHalves, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, Nat.zero_add, hi, decide_true, Bool.true_and,
    show 16*e+i<128 by omega]
  by_cases h : e+k<8
  · rw [ite_eq_left (by omega), Nat.mod_eq_of_lt h]
    exact congrArg _ (by omega)
  · rw [ite_eq_right (by omega), Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega : e+k-8<8)]
    exact congrArg _ (by omega)

def addHalves (x y : BitVec 128) : BitVec 128 := VArr.h8.map2 (fun _ a b => a+b) x y

def sumStep (x : BitVec 128) (k : Nat) : BitVec 128 := addHalves x (rotateHalves x k)

def horizontal (x : BitVec 128) : BitVec 128 := sumStep (sumStep (sumStep x 4) 2) 1

def sum8 (x : BitVec 128) : BitVec 16 :=
  vhalf x 0 + vhalf x 1 + vhalf x 2 + vhalf x 3 +
  vhalf x 4 + vhalf x 5 + vhalf x 6 + vhalf x 7

theorem sumStep_half (x : BitVec 128) {k e : Nat} (hk : k<8) (he : e<8) :
    vhalf (sumStep x k) e = vhalf x e + vhalf x ((e+k)%8) := by
  rw [sumStep,addHalves,vhalf_map2 _ _ _ he,rotate_half x hk he]

theorem horizontal_low (x : BitVec 128) : vhalf (horizontal x) 0 = sum8 x := by
  simp only [horizontal,sumStep_half _ (by decide : 1<8) (by decide : 0<8),
    Nat.reduceAdd,Nat.reduceMod,
    sumStep_half _ (by decide : 2<8) (by decide : 0<8),
    sumStep_half _ (by decide : 2<8) (by decide : 1<8),
    sumStep_half _ (by decide : 4<8) (by decide : 0<8),
    sumStep_half _ (by decide : 4<8) (by decide : 1<8),
    sumStep_half _ (by decide : 4<8) (by decide : 2<8),
    sumStep_half _ (by decide : 4<8) (by decide : 3<8),sum8]
  ac_rfl

/-- The exact six vector instructions before UMOV. -/
def sumCode : List Instr :=
 [.vop (.ext .v2 .v1 .v1 8),.vop (.add .h8 .v1 .v1 .v2),
 .vop (.ext .v2 .v1 .v1 4),.vop (.add .h8 .v1 .v1 .v2),
 .vop (.ext .v2 .v1 .v1 2),.vop (.add .h8 .v1 .v1 .v2)]

theorem sumCode_ok (s : State) :
    WP isa (.block sumCode) s fun t => VChg [.v1,.v2] s t ∧
      t.v .v1 = horizontal (s.v .v1) := by
  refine wp_vop (d := .v2) rfl fun a ha =>
    wp_vop (d := .v1) rfl fun b hb =>
    wp_vop (d := .v2) rfl fun c hc =>
    wp_vop (d := .v1) rfl fun d hd =>
    wp_vop (d := .v2) rfl fun e he =>
    wp_vop (d := .v1) rfl fun t ht => wp_nil ?_
  refine ⟨(((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans he.chg).trans
    ht.chg).mono (by decide), ?_⟩
  rw [ht.v, he.get .v1, he.v, hd.v, hc.get .v1, hc.v, hb.v, ha.get .v1, ha.v]
  rfl

end VG.Proof.MlKem.AArch64.Rej8
