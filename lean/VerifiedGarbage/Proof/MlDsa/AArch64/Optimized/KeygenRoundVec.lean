import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenRound
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound

theorem cadd_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (k : ∀t,VChg [.v0,.v7] s t →
      (∀e<4,vword (t.v .v0) e=Inverse.signCorrected (vword (s.v .v0) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (cadd .v0++rest)) s Q := by
  refine wp_vop (d:=.v7) rfl fun a ha => wp_vop (d:=.v7) rfl fun b hb =>
    wp_vop (d:=.v0) rfl fun t ht => ?_
  refine k t ((ha.chg.trans hb.chg).trans ht.chg |>.mono (by simp)) ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.get .v0 (by decide),ha.get .v0 (by decide),
    hb.v,Inverse.word_and,ha.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v16 (by decide),hq e he]
  rfl

theorem arithmetic_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v17) e=4095#32)
    (k : ∀t,VChg [.v0,.v1,.v2,.v7] s t →
      (∀e<4,vword (t.v .v1) e=highWord (vword (s.v .v0) e)) →
      (∀e<4,vword (t.v .v0) e=lowWord (vword (s.v .v0) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (arithmetic++rest)) s Q := by
  simp only [arithmetic,List.cons_append,List.nil_append]
  refine wp_vop (d:=.v1) rfl fun a ha => wp_vop (d:=.v1) rfl fun b hb =>
    wp_vop (d:=.v2) rfl fun c hc' => wp_vop (d:=.v0) rfl fun d hd => ?_
  have hk : VChg [.v0,.v1,.v2] s d := (((ha.chg.trans hb.chg).trans hc'.chg).trans hd.chg).mono (by simp)
  have high : ∀e<4,vword (d.v .v1) e=highWord (vword (s.v .v0) e) := by
    intro e he
    rw [hd.get .v1 (by decide),hc'.get .v1 (by decide),hb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,hc e he]
    rfl
  have raw : ∀e<4,vword (d.v .v0) e=rawWord (vword (s.v .v0) e) := by
    intro e he
    rw [hd.v,VG.AArch64.vword_map2 _ _ _ he,hc'.get .v0 (by decide),hb.get .v0 (by decide),ha.get .v0 (by decide),
      hc'.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,hc e he]
    rfl
  refine cadd_ok (by intro e he; rw [hk.get .v16 (by decide)]; exact hq e he) fun t ht hv =>
    k t ((hk.trans ht).mono (by simp)) ?_ ?_
  · intro e he; rw [ht.get .v1 (by decide)]; exact high e he
  · intro e he; rw [hv e he,raw e he]; rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
