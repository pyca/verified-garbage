import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowHf2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Impl.MlDsa.AArch64.Round

def lowWrap (g : Nat) (d t : VReg) : List Instr :=
 if g==261888 then [.vop (.logic .and d d .v14)] else
 [.vop (.sub .s4 t d .v14),.vop (.shift .sshr .s4 t t 31),.vop (.logic .and d d t)]
def lowWrapWord (g : Nat) (w : BitVec 32) : BitVec 32 :=
 if g==261888 then w &&& 15 else w &&& BitVec.sshiftRight (w-BitVec.ofNat 32 (dMod g)) 31

def lowWrapTwo (g : Nat) (q : VReg) : List Instr :=
 ((lowWrap g .v26 .v25).zip (lowWrap g .v28 q)).flatMap fun (x,y) => [x,y]

theorem lowWrapTwo_ok {g : Nat} {q : VReg}
    (hq25 : q≠.v25) (hq26 : q≠.v26) (hq28 : q≠.v28)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v,VChg [.v25,q,.v26,.v28] s v →
      (∀e<4,vword (v.v .v26) e=lowWrapWord g (vword (s.v .v26) e)) →
      (∀e<4,vword (v.v .v28) e=lowWrapWord g (vword (s.v .v28) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowWrapTwo g q++rest)) s Q := by
  unfold lowWrapTwo lowWrap
  by_cases hg : g==261888
  · simp only [hg,ite_true,List.zip_cons_cons,List.zip_nil_left,List.flatMap_cons,List.flatMap_nil,
      List.cons_append,List.nil_append]
    refine wp_vop (d := .v26) rfl fun s1 h1 => wp_vop (d := .v28) rfl fun s2 h2 =>
      k s2 ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · intro e he
      rw [h2.get .v26 (by decide),h1.v,Inverse.word_and,h14 e he]
      simp only [lowWrapWord,hg,ite_true]
      rfl
    · intro e he
      rw [h2.v,Inverse.word_and,h1.get .v28 (by decide),h1.get .v14 (by decide),h14 e he]
      simp only [lowWrapWord,hg,ite_true]
      rfl
  · simp only [hg]
    refine wp_vop (d := .v25) rfl fun s1 h1 => wp_vop (d := q) rfl fun s2 h2 =>
      wp_vop (d := .v25) rfl fun s3 h3 => wp_vop (d := q) rfl fun s4 h4 =>
      wp_vop (d := .v26) rfl fun s5 h5 => wp_vop (d := .v28) rfl fun s6 h6 => ?_
    refine k s6 (((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg |>.mono (by simp)) ?_ ?_
    · intro e he
      rw [h6.get .v26 (by decide),h5.v,Inverse.word_and,
        h4.get .v26 (Ne.symm hq26),h3.get .v26 (by decide),h2.get .v26 (Ne.symm hq26),h1.get .v26 (by decide),
        h4.get .v25 (Ne.symm hq25),h3.v,VG.AArch64.vword_map2 _ _ _ he,
        h2.get .v25 (Ne.symm hq25),h1.v,VG.AArch64.vword_map2 _ _ _ he,h14 e he]
      simp only [lowWrapWord,hg]
      rfl
    · intro e he
      rw [h6.v,Inverse.word_and,
        h5.get .v28 (by decide),h4.get .v28 (Ne.symm hq28),h3.get .v28 (by decide),h2.get .v28 (Ne.symm hq28),h1.get .v28 (by decide),
        h5.get q hq26,h4.v,VG.AArch64.vword_map2 _ _ _ he,
        h3.get q hq25,h2.v,VG.AArch64.vword_map2 _ _ _ he,
        h1.get .v28 (by decide),h1.get .v14 (by decide),h14 e he]
      simp only [lowWrapWord,hg]
      rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired
