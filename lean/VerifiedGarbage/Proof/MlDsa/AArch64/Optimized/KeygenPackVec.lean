module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlDsa.AArch64.Optimized.KeygenPackWord`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa

def encoded (b : Nat) (x : BitVec 32) : BitVec 32 :=
  Inverse.signCorrected (BitVec.ofNat 32 b-x)

theorem encoded_int {b : Nat} {x : BitVec 32} (hb : b<q) (hx : x.toNat<q) :
    (BitVec.ofNat 32 b-x).toInt=(b:Int)-x.toNat := by
  have hq : q=8380417 := rfl
  have ht := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 b-x)
  rw [BitVec.toNat_sub,BitVec.toNat_ofNat] at ht
  omega_using [hb, hx, hq, ht]

theorem encoded_nat {b : Nat} {x : BitVec 32} (hb : b<q) (hx : x.toNat<q) :
    (encoded b x).toNat=(b+q-x.toNat)%q := by
  have hq : q=8380417 := rfl
  have hv := encoded_int hb hx
  have hi := Inverse.signCorrected_int (BitVec.ofNat 32 b-x) (by rw [hv]; omega_using [hx, hq]) (by rw [hv]; omega_using [hb, hq])
  rw [hv] at hi
  have ht := BitVec.toInt_eq_toNat_cond (encoded b x)
  change (encoded b x).toInt=_ at hi
  rw [hq]
  by_cases h : x.toNat≤b
  · rw [ite_eq_right (by omega_using [h])] at hi
    omega
  · rw [ite_eq_left (by omega_using [h])] at hi
    omega

theorem encoded_bpVal {b : Nat} {x : BitVec 32} (hb : b<q) (hx : x.toNat<q) :
    (encoded b x).toNat=Pack.bpVal b x := by
  rw [encoded_nat hb hx]
  unfold Pack.bpVal
  rw [show x.setWidth 64=BitVec.ofNat 64 x.toNat by simp,Pack.subModQ_toNat hb hx]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

theorem convert_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (r : VReg) (hr : r∉[VReg.v4,.v16,.v17]) (b : Nat)
    (hb : ∀e<4,vword (s.v .v16) e=BitVec.ofNat 32 b)
    (hq : ∀e<4,vword (s.v .v17) e=8380417#32)
    (k : ∀t,VChg [r,.v4] s t →
      (∀e<4,vword (t.v r) e=encoded b (vword (s.v r) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (convert r++rest)) s Q := by
  have hr4 : r≠.v4 := by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact hr.1
  have hr17 : r≠.v17 := by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact hr.2.2
  refine wp_vop (d:=r) rfl fun a ha => wp_vop (d:=.v4) rfl fun c hc =>
    wp_vop (d:=.v4) rfl fun d hd => wp_vop (d:=r) rfl fun t ht => ?_
  refine k t ((((ha.chg.trans hc.chg).trans hd.chg).trans ht.chg).mono (by simp)) ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hd.get r hr4,hc.get r hr4,
    hd.v,Inverse.word_and,hc.v,VG.AArch64.vword_map2 _ _ _ he,
    hc.get .v17 (by decide),ha.get .v17 (Ne.symm hr17),hq e he,
    ha.v,VG.AArch64.vword_map2 _ _ _ he,hb e he]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
