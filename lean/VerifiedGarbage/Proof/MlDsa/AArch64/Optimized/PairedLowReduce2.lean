import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLane

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

def reduceTwo (a t b u : VReg) : List Instr :=
 ((reduceRegs a t).zip (reduceRegs b u)).flatMap fun (x,y) => [x,y]

/-- The two reductions execute in the measured alternating instruction order. -/
theorem reduceTwo_ok {a t b u : VReg}
    (hat : a≠t) (hab : a≠b) (hau : a≠u) (htb : t≠b) (htu : t≠u) (hbu : b≠u)
    (hregs : ∀r∈[a,t,b,u],r≠.v8 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v,VChg [a,t,b,u] s v →
      (∀e<4,vword (v.v a) e=Response.reduceWord (vword (s.v a) e)) →
      (∀e<4,vword (v.v b) e=Response.reduceWord (vword (s.v b) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (reduceTwo a t b u++rest)) s Q := by
  refine wp_vop (d := t) rfl fun s1 h1 => wp_vop (d := u) rfl fun s2 h2 =>
    wp_vop (d := t) rfl fun s3 h3 => wp_vop (d := u) rfl fun s4 h4 =>
    wp_vop (d := a) rfl fun s5 h5 => wp_vop (d := b) rfl fun s6 h6 => ?_
  have hqT := Ne.symm (hregs t (by simp)).2
  have hqU := Ne.symm (hregs u (by simp)).2
  have hqA := Ne.symm (hregs a (by simp)).2
  have hcT := Ne.symm (hregs t (by simp)).1
  refine k s6 (((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg |>.mono ?_) ?_ ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [h6.get a hab,h5.v,vword_mapWords3 _ _ _ _ he,
      h4.get a hau,h3.get a hat,h2.get a hau,h1.get a hat,
      h4.get t htu,h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get t htu,h1.v,VG.AArch64.vword_map2 _ _ _ he,
      h4.get .v31 hqU,h3.get .v31 hqT,h2.get .v31 hqU,h1.get .v31 hqT,hq e he,hc e he]
    rfl
  · intro e he
    rw [h6.v,vword_mapWords3 _ _ _ _ he,
      h5.get b (Ne.symm hab),h4.get b hbu,h3.get b (Ne.symm htb),h2.get b hbu,h1.get b (Ne.symm htb),
      h5.get u (Ne.symm hau),h4.v,VG.AArch64.vword_map2 _ _ _ he,
      h3.get u (Ne.symm htu),h2.v,VG.AArch64.vword_map2 _ _ _ he,
      h1.get b (Ne.symm htb),h1.get .v8 hcT,
      h5.get .v31 hqA,h4.get .v31 hqU,h3.get .v31 hqT,h2.get .v31 hqU,h1.get .v31 hqT,hq e he,hc e he]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired
