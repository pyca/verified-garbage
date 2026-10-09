import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec

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
