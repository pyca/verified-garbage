import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (hintWord word_or word_not)

def hintVector : List Instr :=
 [.vop (.sub .s4 .v25 .v11 .v24),.vop (.sub .s4 .v28 .v24 .v12),
  .vop (.logic .orr .v25 .v25 .v28),.vop (.shift .sshr .s4 .v25 .v25 31),
  .vop (.cmeq .s4 .v28 .v24 .v12),.vop (.cmeq .s4 .v26 .v26 .v13),
  .vop (.logic .bic .v28 .v28 .v26),.vop (.logic .orr .v25 .v25 .v28),
  .vop (.shift .ushr .s4 .v25 .v25 31)]

theorem hintVector_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hn : ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e)
    (hz : ∀e<4,vword (s.v .v13) e=0)
    (k : ∀t,VChg [.v25,.v28,.v26] s t → (∀e<4,vword (t.v .v25) e=
      hintWord (vword (s.v .v11) e) (vword (s.v .v24) e) (vword (s.v .v26) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintVector++rest)) s Q := by
  refine wp_vop (d:=.v25) rfl fun a ha => wp_vop (d:=.v28) rfl fun b hb =>
    wp_vop (d:=.v25) rfl fun c hc => wp_vop (d:=.v25) rfl fun d hd =>
    wp_vop (d:=.v28) rfl fun f hf => wp_vop (d:=.v26) rfl fun g hg =>
    wp_vop (d:=.v28) rfl fun h hh => wp_vop (d:=.v25) rfl fun i hi =>
    wp_vop (d:=.v25) rfl fun t ht => ?_
  have hk : VChg [.v25,.v28,.v26] s t :=
    ((((((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans hf.chg).trans hg.chg).trans hh.chg).trans hi.chg).trans ht.chg).mono (by decide)
  refine k t hk ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hi.v,word_or,
    hh.get .v25 (by decide),hg.get .v25 (by decide),hf.get .v25 (by decide),hd.v,
    VG.AArch64.vword_map2 _ _ _ he,hc.v,word_or,hb.get .v25 (by decide),ha.v,
    VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
    ha.get .v24 (by decide),ha.get .v12 (by decide),hn e he,
    hh.v,Inverse.word_and,word_not _ he,hg.v,VG.AArch64.vword_map2 _ _ _ he,
    hf.get .v26 (by decide),hd.get .v26 (by decide),hc.get .v26 (by decide),
    hb.get .v26 (by decide),ha.get .v26 (by decide),
    hf.get .v13 (by decide),hd.get .v13 (by decide),hc.get .v13 (by decide),
    hb.get .v13 (by decide),ha.get .v13 (by decide),hz e he,
    hg.get .v28 (by decide),hf.v,VG.AArch64.vword_map2 _ _ _ he,
    hd.get .v24 (by decide),hc.get .v24 (by decide),hb.get .v24 (by decide),ha.get .v24 (by decide),
    hd.get .v12 (by decide),hc.get .v12 (by decide),hb.get .v12 (by decide),ha.get .v12 (by decide),hn e he]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
