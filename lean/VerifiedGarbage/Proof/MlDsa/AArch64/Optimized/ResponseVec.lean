import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

theorem reduce_ok {d : VReg} (h6 : d≠.v6)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v25) e=4194304#32)
    (k : ∀t,VChg [.v6,d] s t → (∀e<4,vword (t.v d) e=reduceWord (vword (s.v d) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Response.reduce d++rest)) s Q := by
  refine wp_vop (d := .v6) rfl fun a ha => wp_vop (d := .v6) rfl fun b hb =>
    wp_vop (d := d) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,vword_mapWords3 _ _ _ _ he,hb.get d h6,ha.get d h6,
      hb.v,VG.AArch64.vword_map2 _ _ _ he,ha.v,VG.AArch64.vword_map2 _ _ _ he,
      hb.get .v16 (by decide),ha.get .v16 (by decide),hc e he,hq e he]
    rfl

def normMask (x lo width : BitVec 32) : BitVec 32 :=
  if width.toNat≤(x+lo).toNat then -1 else 0

theorem normMask_value {x : BitVec 32} {B : Nat} (hB : 1≤B) (hB' : B≤524288)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) :
    normMask x (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if -(B:Int)<x.toInt ∧ x.toInt<(B:Int) then 0 else -1 := by
  have hn := norm_interval x B hB hB' hl hh
  have hw : (BitVec.ofNat 32 (2*B-1)).toNat=2*B-1 := by
    rw [BitVec.toNat_ofNat]; omega
  unfold normMask
  rw [hw]
  by_cases h : -(B:Int)<x.toInt ∧ x.toInt<(B:Int)
  · rw [ite_eq_left h,ite_eq_right (by have := hn.mpr h; omega)]
  · rw [ite_eq_right h,ite_eq_left (by have := mt hn.mp h; omega)]

theorem minMask (a b : BitVec 32) :
    (if (if a.toNat≤b.toNat then a else b)=b then BitVec.allOnes 32 else 0)=
      (if b.toNat≤a.toNat then -1 else 0) := by
  by_cases h : a.toNat≤b.toNat
  · rw [ite_eq_left h]
    by_cases he : a=b
    · subst b; simp only [ite_true,Nat.le_refl]; rfl
    · rw [ite_eq_right he,ite_eq_right (by intro hh; exact he (BitVec.eq_of_toNat_eq (by omega)))]
  · rw [ite_eq_right h]
    rw [ite_eq_left (show b=b from rfl),ite_eq_left (show b.toNat≤a.toNat by omega)]
    rfl

theorem norm_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v2,.v31] s t → (∀e<4,vword (t.v .v31) e=
      vword (s.v .v31) e ||| normMask (vword (s.v .v0) e)
        (vword (s.v .v27) e) (vword (s.v .v24) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Response.testNorm++rest)) s Q := by
  refine wp_vop (d := .v2) rfl fun a ha => wp_vop (d := .v2) rfl fun b hb =>
    wp_vop (d := .v2) rfl fun c hc => wp_vop (d := .v31) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans hc.chg).trans ht.chg |>.mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v]
    simp only [vword,BitVec.extractLsb'_or]
    change vword (c.v .v31) e ||| vword (c.v .v2) e=_
    rw [hc.get .v31 (by decide),hb.get .v31 (by decide),ha.get .v31 (by decide),
      hc.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      hb.get .v24 (by decide),ha.get .v24 (by decide),ha.v,VG.AArch64.vword_map2 _ _ _ he,minMask]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
