import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask minMask)

theorem reduce_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀t,VChg [.v25,.v24] s t → (∀e<4,vword (t.v .v24) e=reduceWord (vword (s.v .v24) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Paired.reduce++rest)) s Q := by
  refine wp_vop (d := .v25) rfl fun a ha => wp_vop (d := .v25) rfl fun b hb =>
    wp_vop (d := .v24) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,vword_mapWords3 _ _ _ _ he,hb.get .v24 (by decide),ha.get .v24 (by decide),
      hb.v,VG.AArch64.vword_map2 _ _ _ he,ha.v,VG.AArch64.vword_map2 _ _ _ he,
      hb.get .v31 (by decide),ha.get .v31 (by decide),hc e he,hq e he]
    rfl

theorem norm_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v25,.v30] s t → (∀e<4,vword (t.v .v30) e=
      vword (s.v .v30) e ||| normMask (vword (s.v .v24) e)
        (vword (s.v .v9) e) (vword (s.v .v10) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Paired.norm++rest)) s Q := by
  refine wp_vop (d := .v25) rfl fun a ha => wp_vop (d := .v25) rfl fun b hb =>
    wp_vop (d := .v25) rfl fun c hc => wp_vop (d := .v30) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans hc.chg).trans ht.chg |>.mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v]
    simp only [vword,BitVec.extractLsb'_or]
    change vword (c.v .v30) e ||| vword (c.v .v25) e=_
    rw [hc.get .v30 (by decide),hb.get .v30 (by decide),ha.get .v30 (by decide),
      hc.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      hb.get .v10 (by decide),ha.get .v10 (by decide),ha.v,VG.AArch64.vword_map2 _ _ _ he,minMask]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
