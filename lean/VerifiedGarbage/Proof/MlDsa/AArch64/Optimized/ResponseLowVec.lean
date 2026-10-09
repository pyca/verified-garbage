import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoad

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

theorem cadd_ok {d : VReg} (hd : d≠.v7) {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (k : ∀t,VChg [.v7,d] s t →
      (∀e<4,vword (t.v d) e=Inverse.signCorrected (vword (s.v d) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Response.cadd d++rest)) s Q := by
  refine wp_vop (d:=.v7) rfl fun a ha => wp_vop (d:=.v7) rfl fun b hb =>
    wp_vop (d:=d) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.get d hd,ha.get d hd,hb.v,Inverse.word_and,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v16 (by decide),hq e he]
    rfl

def lowCorrection : List Instr :=
  [.vop (.mls .v0 .v1 .v21),.vop (.sub .s4 .v6 .v26 .v0),
    .vop (.shift .sshr .s4 .v6 .v6 31),.vop (.logic .and .v6 .v6 .v16),
    .vop (.sub .s4 .v0 .v0 .v6)]

def lowWord (a h twoG : BitVec 32) : BitVec 32 :=
  let l := a-h*twoG
  l-((4190208#32-l).sshiftRight 31 &&& 8380417#32)

theorem lowCorrection_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hh : ∀e<4,vword (s.v .v26) e=4190208#32)
    (k : ∀t,VChg [.v0,.v6] s t → (∀e<4,vword (t.v .v0) e=
      lowWord (vword (s.v .v0) e) (vword (s.v .v1) e) (vword (s.v .v21) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (lowCorrection++rest)) s Q := by
  refine wp_vop (d:=.v0) rfl fun a ha => wp_vop (d:=.v6) rfl fun b hb =>
    wp_vop (d:=.v6) rfl fun c hc => wp_vop (d:=.v6) rfl fun d hd =>
    wp_vop (d:=.v0) rfl fun t ht => ?_
  have hk : VChg [.v0,.v6] s t :=
    ((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans ht.chg).mono (by decide)
  refine k t hk ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hd.get .v0 (by decide),hc.get .v0 (by decide),
    hb.get .v0 (by decide),hd.v,Inverse.word_and,hc.v,VG.AArch64.vword_map2 _ _ _ he,
    hb.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v26 (by decide),hh e he,
    hc.get .v16 (by decide),hb.get .v16 (by decide),ha.get .v16 (by decide),hq e he,
    ha.v,vword_mapWords3 _ _ _ _ he]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
