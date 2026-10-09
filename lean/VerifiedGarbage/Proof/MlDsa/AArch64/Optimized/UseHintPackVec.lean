import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

 theorem csub_ok {s : State} {rest : List Instr} {Q : State→Prop}
    (k : ∀t,VChg [.v6,.v7] s t →
      (∀e<4,vword (t.v .v6) e=csub (vword (s.v .v20) e) (vword (s.v .v6) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.UseHintPack.csub .v6 .v20++rest)) s Q := by
  refine wp_vop (d:=.v7) rfl fun a ha=>wp_vop (d:=.v6) rfl fun t ht=>?_
  refine k t ((ha.chg.trans ht.chg).mono (by decide)) ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v6,ha.v,VG.AArch64.vword_map2 _ _ _ he]
  rfl

 def adjustCode : List Instr :=
  [.vop (.mul .v26 .v6 .v21),.vop (.sub .s4 .v26 .v26 .v4),
   .vop (.shift .ushr .s4 .v26 .v26 31),.vop (.shift .shl .s4 .v26 .v26 1),
   .vop (.sub .s4 .v26 .v26 .v22),.vop (.cmeq .s4 .v5 .v5 .v23),
   .vop (.logic .bic .v26 .v26 .v5),.vop (.add .s4 .v6 .v6 .v26),
   .vop (.add .s4 .v6 .v6 .v20)]

 theorem adjust_ok {s : State} {rest : List Instr} {Q : State→Prop}
    (hzero : ∀e<4,vword (s.v .v23) e=0) (hone : ∀e<4,vword (s.v .v22) e=1)
    (k : ∀t,VChg [.v5,.v6,.v26] s t →
      (∀e<4,vword (t.v .v6) e=
        vword (s.v .v6) e+
        (if vword (s.v .v5) e=0 then (0 : BitVec 32) else
          (((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1)-1)+
        vword (s.v .v20) e) → WP isa (.block rest) t Q) :
    WP isa (.block (adjustCode++rest)) s Q := by
  refine wp_vop (d:=.v26) rfl fun s1 h1=>wp_vop (d:=.v26) rfl fun s2 h2=>
    wp_vop (d:=.v26) rfl fun s3 h3=>wp_vop (d:=.v26) rfl fun s4 h4=>
    wp_vop (d:=.v26) rfl fun s5 h5=>wp_vop (d:=.v5) rfl fun s6 h6=>
    wp_vop (d:=.v26) rfl fun s7 h7=>wp_vop (d:=.v6) rfl fun s8 h8=>
    wp_vop (d:=.v6) rfl fun t h9=>?_
  have hk := (((((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg).trans h9.chg
  refine k t (hk.mono (by decide)) ?_
  intro e he
  have e1 : vword (s1.v .v26) e=vword (s.v .v6) e*vword (s.v .v21) e := by
    rw [h1.v,VG.AArch64.vword_map2 _ _ _ he]
  have e2 : vword (s2.v .v26) e=vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e := by
    rw [h2.v,VG.AArch64.vword_map2 _ _ _ he,e1,h1.get .v4]
  have e3 : vword (s3.v .v26) e=(vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31 := by
    rw [h3.v,VG.AArch64.vword_map2 _ _ _ he,e2]; rfl
  have e4 : vword (s4.v .v26) e=((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1 := by
    rw [h4.v,VG.AArch64.vword_map2 _ _ _ he,e3]; rfl
  have e5 : vword (s5.v .v26) e=(((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1)-1 := by
    rw [h5.v,VG.AArch64.vword_map2 _ _ _ he,e4,h4.get .v22,h3.get .v22,h2.get .v22,h1.get .v22,hone e he]
  have e6 : vword (s6.v .v5) e=if vword (s.v .v5) e=0 then (-1 : BitVec 32) else 0 := by
    rw [h6.v,VG.AArch64.vword_map2 _ _ _ he,
      h5.get .v5,h4.get .v5,h3.get .v5,h2.get .v5,h1.get .v5,
      h5.get .v23,h4.get .v23,h3.get .v23,h2.get .v23,h1.get .v23,hzero e he]
    rfl
  have e7 : vword (s7.v .v26) e=if vword (s.v .v5) e=0 then (0 : BitVec 32) else
      (((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1)-1 := by
    rw [h7.v]
    change vword (s6.v .v26 &&& ~~~s6.v .v5) e=_
    have hand (a b : BitVec 128) : vword (a &&& b) e=vword a e &&& vword b e := by
      simp only [vword,BitVec.extractLsb'_and]
    rw [hand,Response.word_not _ he]
    rw [h6.get .v26,e5,e6]
    split
    · simp
    · exact BitVec.and_allOnes
  have e8 : vword (s8.v .v6) e=vword (s.v .v6) e+
      (if vword (s.v .v5) e=0 then (0 : BitVec 32) else
        (((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1)-1) := by
    rw [h8.v,VG.AArch64.vword_map2 _ _ _ he,e7,
      h7.get .v6,h6.get .v6,h5.get .v6,h4.get .v6,h3.get .v6,h2.get .v6,h1.get .v6]
  rw [h9.v,VG.AArch64.vword_map2 _ _ _ he,e8,
    h8.get .v20,h7.get .v20,h6.get .v20,h5.get .v20,h4.get .v20,h3.get .v20,h2.get .v20,h1.get .v20]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
