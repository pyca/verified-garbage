import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def hintVector : List Instr :=
 [.vop (.sub .s4 .v2 .v17 .v0),.vop (.sub .s4 .v3 .v0 .v18),
  .vop (.logic .orr .v2 .v2 .v3),.vop (.shift .sshr .s4 .v2 .v2 31),
  .vop (.cmeq .s4 .v3 .v0 .v18),.vop (.cmeq .s4 .v4 .v4 .v23),
  .vop (.logic .bic .v3 .v3 .v4),.vop (.logic .orr .v2 .v2 .v3),
  .vop (.shift .ushr .s4 .v2 .v2 31)]

theorem word_or (a b : BitVec 128) (e : Nat) :
    vword (a ||| b) e=vword a e ||| vword b e := by
  simp only [vword,BitVec.extractLsb'_or]

theorem word_not (a : BitVec 128) {e : Nat} (he : e<4) :
    vword (~~~a) e = ~~~vword a e := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [vword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_not]
  simp (disch := omega) only [decide_eq_true,Bool.true_and]

theorem hintVector_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hn : ∀e<4,vword (s.v .v18) e= -vword (s.v .v17) e)
    (hz : ∀e<4,vword (s.v .v23) e=0)
    (k : ∀t,VChg [.v2,.v3,.v4] s t → (∀e<4,vword (t.v .v2) e=
      hintWord (vword (s.v .v17) e) (vword (s.v .v0) e) (vword (s.v .v4) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintVector++rest)) s Q := by
  refine wp_vop (d:=.v2) rfl fun a ha => wp_vop (d:=.v3) rfl fun b hb =>
    wp_vop (d:=.v2) rfl fun c hc => wp_vop (d:=.v2) rfl fun d hd =>
    wp_vop (d:=.v3) rfl fun f hf => wp_vop (d:=.v4) rfl fun g hg =>
    wp_vop (d:=.v3) rfl fun h hh => wp_vop (d:=.v2) rfl fun i hi =>
    wp_vop (d:=.v2) rfl fun t ht => ?_
  have hk : VChg [.v2,.v3,.v4] s t :=
    ((((((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans hf.chg).trans hg.chg).trans hh.chg).trans hi.chg).trans ht.chg).mono (by decide)
  refine k t hk ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hi.v,word_or,
    hh.get .v2 (by decide),hg.get .v2 (by decide),hf.get .v2 (by decide),hd.v,
    VG.AArch64.vword_map2 _ _ _ he,hc.v,word_or,hb.get .v2 (by decide),ha.v,
    VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
    ha.get .v0 (by decide),ha.get .v18 (by decide),hn e he,
    hh.v,Inverse.word_and,word_not _ he,hg.v,VG.AArch64.vword_map2 _ _ _ he,
    hf.get .v4 (by decide),hd.get .v4 (by decide),hc.get .v4 (by decide),
    hb.get .v4 (by decide),ha.get .v4 (by decide),
    hf.get .v23 (by decide),hd.get .v23 (by decide),hc.get .v23 (by decide),
    hb.get .v23 (by decide),ha.get .v23 (by decide),hz e he,
    hg.get .v3 (by decide),hf.v,VG.AArch64.vword_map2 _ _ _ he,
    hd.get .v0 (by decide),hc.get .v0 (by decide),hb.get .v0 (by decide),ha.get .v0 (by decide),
    hd.get .v18 (by decide),hc.get .v18 (by decide),hb.get .v18 (by decide),ha.get .v18 (by decide),hn e he]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
